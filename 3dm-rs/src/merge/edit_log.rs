//! Edit operation logging for the merge algorithm.
//!
//! This module tracks the edit operations performed during the merge process,
//! including inserts, updates, copies, moves, and deletes.

use std::io::Write;

use crate::node::NodeRef;

/// Types of edit operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EditType {
    /// Node was inserted (new content).
    Insert,
    /// Node content was updated.
    Update,
    /// Node was copied from base.
    Copy,
    /// Node was moved from original location.
    Move,
    /// Node was deleted.
    Delete,
}

impl EditType {
    /// Returns the XML tag name for this edit type.
    pub fn tag_name(&self) -> &'static str {
        match self {
            EditType::Insert => "insert",
            EditType::Update => "update",
            EditType::Copy => "copy",
            EditType::Move => "move",
            EditType::Delete => "delete",
        }
    }
}

/// A single edit operation entry.
#[derive(Debug, Clone)]
pub struct EditEntry {
    /// The type of edit operation.
    pub edit_type: EditType,
    /// The node being edited (branch node for most ops, base for delete).
    pub node: Option<NodeRef>,
    /// Whether the node is from the left tree.
    pub is_left_tree: bool,
}

/// Log of edit operations performed during merge.
///
/// The edit log supports checkpoints for transactional semantics -
/// operations can be rolled back if a merge path fails.
#[derive(Debug, Default)]
pub struct EditLog {
    /// List of edit operations.
    edits: Vec<EditEntry>,
    /// Stack of checkpoint positions for rollback.
    checkpoints: Vec<usize>,
}

impl EditLog {
    /// Creates a new empty edit log.
    pub fn new() -> Self {
        EditLog {
            edits: Vec::new(),
            checkpoints: Vec::new(),
        }
    }

    /// Records an insert operation.
    pub fn insert(&mut self, node: Option<NodeRef>) {
        let is_left = node
            .as_ref()
            .map(crate::node::BranchNode::is_left_tree)
            .unwrap_or(true);

        self.edits.push(EditEntry {
            edit_type: EditType::Insert,
            node,
            is_left_tree: is_left,
        });
    }

    /// Records an update operation.
    pub fn update(&mut self, node: Option<NodeRef>) {
        let is_left = node
            .as_ref()
            .map(crate::node::BranchNode::is_left_tree)
            .unwrap_or(true);

        self.edits.push(EditEntry {
            edit_type: EditType::Update,
            node,
            is_left_tree: is_left,
        });
    }

    /// Records a copy operation.
    pub fn copy(&mut self, node: Option<NodeRef>) {
        let is_left = node
            .as_ref()
            .map(crate::node::BranchNode::is_left_tree)
            .unwrap_or(true);

        self.edits.push(EditEntry {
            edit_type: EditType::Copy,
            node,
            is_left_tree: is_left,
        });
    }

    /// Records a move operation.
    pub fn r#move(&mut self, node: Option<NodeRef>) {
        let is_left = node
            .as_ref()
            .map(crate::node::BranchNode::is_left_tree)
            .unwrap_or(true);

        self.edits.push(EditEntry {
            edit_type: EditType::Move,
            node,
            is_left_tree: is_left,
        });
    }

    /// Records a delete operation.
    pub fn delete(&mut self, node: Option<NodeRef>) {
        // For delete, node is a base node, so is_left_tree doesn't apply
        self.edits.push(EditEntry {
            edit_type: EditType::Delete,
            node,
            is_left_tree: true,
        });
    }

    /// Creates a checkpoint for potential rollback.
    pub fn checkpoint(&mut self) {
        self.checkpoints.push(self.edits.len());
    }

    /// Rolls back to the last checkpoint, discarding operations since then.
    pub fn rewind(&mut self) {
        if let Some(pos) = self.checkpoints.pop() {
            self.edits.truncate(pos);
        }
    }

    /// Commits the operations since the last checkpoint.
    pub fn commit(&mut self) {
        self.checkpoints.pop();
    }

    /// Returns the number of edit operations.
    pub fn edit_count(&self) -> usize {
        self.edits.len()
    }

    /// Returns a reference to the edit operations.
    pub fn edits(&self) -> &[EditEntry] {
        &self.edits
    }

    /// Counts operations by type.
    pub fn count_by_type(&self, edit_type: EditType) -> usize {
        self.edits
            .iter()
            .filter(|e| e.edit_type == edit_type)
            .count()
    }

    /// Writes the edit log as XML.
    pub fn write_xml<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writeln!(writer, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>")?;
        writeln!(writer, "<edits>")?;

        for entry in &self.edits {
            self.write_entry(writer, entry)?;
        }

        writeln!(writer, "</edits>")?;
        Ok(())
    }

    /// Writes a single edit entry as XML.
    fn write_entry<W: Write>(&self, writer: &mut W, entry: &EditEntry) -> std::io::Result<()> {
        let tag = entry.edit_type.tag_name();
        let tree = if entry.is_left_tree {
            "branch1"
        } else {
            "branch2"
        };

        write!(writer, "  <{}", tag)?;

        if let Some(node) = &entry.node {
            let path = get_node_path(node);
            write!(writer, " path=\"{}\"", escape_xml(&path))?;

            // For update/copy/move, include base source
            if entry.edit_type != EditType::Insert && entry.edit_type != EditType::Delete {
                if let Some(base) = crate::node::BranchNode::base_match(node) {
                    let base_path = get_node_path(&base);
                    write!(writer, " src=\"{}\"", escape_xml(&base_path))?;
                }
            }
        }

        write!(writer, " originTree=\"{}\"", tree)?;
        writeln!(writer, " />")?;

        Ok(())
    }
}

/// Escapes special characters in XML attribute values.
fn escape_xml(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// Gets a path string for a node.
fn get_node_path(node: &NodeRef) -> String {
    use crate::node::XmlContent;

    let mut parts = Vec::new();
    let mut current = Some(node.clone());

    while let Some(n) = current {
        let borrowed = n.borrow();
        let name = match borrowed.content() {
            Some(XmlContent::Element(e)) => e.qname().to_string(),
            Some(XmlContent::Text(_)) => "#text".to_string(),
            Some(XmlContent::Comment(_)) => "#comment".to_string(),
            None => "#node".to_string(),
        };

        let pos = borrowed.child_pos();
        if pos >= 0 {
            parts.push(format!("{}[{}]", name, pos));
        } else {
            parts.push(name);
        }

        current = borrowed.parent().upgrade();
    }

    parts.reverse();
    if parts.is_empty() {
        "/".to_string()
    } else {
        format!("/{}", parts.join("/"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edit_type_tag_names() {
        assert_eq!(EditType::Insert.tag_name(), "insert");
        assert_eq!(EditType::Update.tag_name(), "update");
        assert_eq!(EditType::Copy.tag_name(), "copy");
        assert_eq!(EditType::Move.tag_name(), "move");
        assert_eq!(EditType::Delete.tag_name(), "delete");
    }

    #[test]
    fn test_edit_log_empty() {
        let log = EditLog::new();
        assert_eq!(log.edit_count(), 0);
    }

    #[test]
    fn test_edit_log_operations() {
        let mut log = EditLog::new();

        log.insert(None);
        log.update(None);
        log.copy(None);
        log.r#move(None);
        log.delete(None);

        assert_eq!(log.edit_count(), 5);
        assert_eq!(log.count_by_type(EditType::Insert), 1);
        assert_eq!(log.count_by_type(EditType::Update), 1);
        assert_eq!(log.count_by_type(EditType::Copy), 1);
        assert_eq!(log.count_by_type(EditType::Move), 1);
        assert_eq!(log.count_by_type(EditType::Delete), 1);
    }

    #[test]
    fn test_edit_log_checkpoint_rewind() {
        let mut log = EditLog::new();

        log.insert(None);
        log.insert(None);
        assert_eq!(log.edit_count(), 2);

        log.checkpoint();
        log.insert(None);
        log.insert(None);
        assert_eq!(log.edit_count(), 4);

        log.rewind();
        assert_eq!(log.edit_count(), 2);
    }

    #[test]
    fn test_edit_log_checkpoint_commit() {
        let mut log = EditLog::new();

        log.insert(None);
        log.checkpoint();
        log.insert(None);
        log.commit();
        log.insert(None);

        assert_eq!(log.edit_count(), 3);
    }

    #[test]
    fn test_nested_checkpoints() {
        let mut log = EditLog::new();

        log.insert(None); // 1
        log.checkpoint();
        log.insert(None); // 2
        log.checkpoint();
        log.insert(None); // 3
        assert_eq!(log.edit_count(), 3);

        log.rewind(); // Back to 2
        assert_eq!(log.edit_count(), 2);

        log.rewind(); // Back to 1
        assert_eq!(log.edit_count(), 1);
    }
}
