//! Conflict logging for the merge algorithm.
//!
//! This module provides structures for tracking conflicts and warnings
//! that occur during the 3-way merge process.

use std::io::Write;

use crate::node::NodeRef;

/// Types of conflicts that can occur during merge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConflictType {
    /// Content update conflict.
    Update,
    /// Node deletion conflict.
    Delete,
    /// Node insertion conflict.
    Insert,
    /// Node move conflict.
    Move,
}

impl ConflictType {
    /// Returns the XML tag name for this conflict type.
    pub fn tag_name(&self) -> &'static str {
        match self {
            ConflictType::Update => "update",
            ConflictType::Delete => "delete",
            ConflictType::Insert => "insert",
            ConflictType::Move => "move",
        }
    }
}

/// A single conflict or warning entry.
#[derive(Debug, Clone)]
pub struct ConflictEntry {
    /// The type of conflict.
    pub conflict_type: ConflictType,
    /// Description of the conflict.
    pub text: String,
    /// The base node involved (if any).
    pub base: Option<NodeRef>,
    /// The branch 1 (left) node involved (if any).
    pub branch1: Option<NodeRef>,
    /// The branch 2 (right) node involved (if any).
    pub branch2: Option<NodeRef>,
    /// Path in the merged tree.
    pub merge_path: String,
    /// Whether this is a list-level conflict (vs node-level).
    pub is_list: bool,
}

/// Log of conflicts and warnings encountered during merge.
#[derive(Debug, Default)]
pub struct ConflictLog {
    /// List of conflicts (merge failures).
    conflicts: Vec<ConflictEntry>,
    /// List of warnings (potential issues but merge succeeded).
    warnings: Vec<ConflictEntry>,
    /// Current path in the merge tree.
    current_path: Vec<String>,
}

impl ConflictLog {
    /// Creates a new empty conflict log.
    pub fn new() -> Self {
        ConflictLog {
            conflicts: Vec::new(),
            warnings: Vec::new(),
            current_path: Vec::new(),
        }
    }

    /// Pushes a path component onto the current path.
    pub fn push_path(&mut self, component: &str) {
        self.current_path.push(component.to_string());
    }

    /// Pops a path component from the current path.
    pub fn pop_path(&mut self) {
        self.current_path.pop();
    }

    /// Returns the current path as a string.
    pub fn path_string(&self) -> String {
        if self.current_path.is_empty() {
            "/".to_string()
        } else {
            format!("/{}", self.current_path.join("/"))
        }
    }

    /// Adds a list-level conflict.
    pub fn add_list_conflict(
        &mut self,
        conflict_type: ConflictType,
        text: &str,
        base: Option<NodeRef>,
        branch_a: Option<NodeRef>,
        branch_b: Option<NodeRef>,
    ) {
        self.add(true, false, conflict_type, text, base, branch_a, branch_b);
    }

    /// Adds a list-level warning.
    pub fn add_list_warning(
        &mut self,
        conflict_type: ConflictType,
        text: &str,
        base: Option<NodeRef>,
        branch_a: Option<NodeRef>,
        branch_b: Option<NodeRef>,
    ) {
        self.add(true, true, conflict_type, text, base, branch_a, branch_b);
    }

    /// Adds a node-level conflict.
    pub fn add_node_conflict(
        &mut self,
        conflict_type: ConflictType,
        text: &str,
        base: Option<NodeRef>,
        branch_a: Option<NodeRef>,
        branch_b: Option<NodeRef>,
    ) {
        self.add(false, false, conflict_type, text, base, branch_a, branch_b);
    }

    /// Adds a node-level warning.
    pub fn add_node_warning(
        &mut self,
        conflict_type: ConflictType,
        text: &str,
        base: Option<NodeRef>,
        branch_a: Option<NodeRef>,
        branch_b: Option<NodeRef>,
    ) {
        self.add(false, true, conflict_type, text, base, branch_a, branch_b);
    }

    /// Internal method to add an entry.
    #[allow(clippy::too_many_arguments)]
    fn add(
        &mut self,
        is_list: bool,
        is_warning: bool,
        conflict_type: ConflictType,
        text: &str,
        base: Option<NodeRef>,
        branch_a: Option<NodeRef>,
        branch_b: Option<NodeRef>,
    ) {
        // Normalize so branch1 is left tree, branch2 is right tree
        let (branch1, branch2) = Self::normalize_branches(branch_a, branch_b);

        let entry = ConflictEntry {
            conflict_type,
            text: text.to_string(),
            base,
            branch1,
            branch2,
            merge_path: self.path_string(),
            is_list,
        };

        if is_warning {
            self.warnings.push(entry);
        } else {
            self.conflicts.push(entry);
        }
    }

    /// Normalizes branch references so branch1 is left and branch2 is right.
    fn normalize_branches(
        branch_a: Option<NodeRef>,
        branch_b: Option<NodeRef>,
    ) -> (Option<NodeRef>, Option<NodeRef>) {
        use crate::node::BranchNode;

        let (ba, bb) = match (branch_a, branch_b) {
            (None, b) => (b, None),
            (a, b) => (a, b),
        };

        match &ba {
            Some(node) if BranchNode::is_left_tree(node) => (ba, bb),
            Some(_) => (bb, ba),
            None => (None, None),
        }
    }

    /// Returns true if there are any conflicts.
    pub fn has_conflicts(&self) -> bool {
        !self.conflicts.is_empty()
    }

    /// Returns the number of conflicts.
    pub fn conflict_count(&self) -> usize {
        self.conflicts.len()
    }

    /// Returns the number of warnings.
    pub fn warning_count(&self) -> usize {
        self.warnings.len()
    }

    /// Returns a reference to the conflicts.
    pub fn conflicts(&self) -> &[ConflictEntry] {
        &self.conflicts
    }

    /// Returns a reference to the warnings.
    pub fn warnings(&self) -> &[ConflictEntry] {
        &self.warnings
    }

    /// Writes the conflict log as XML.
    pub fn write_xml<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writeln!(writer, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>")?;
        writeln!(writer, "<conflictlist>")?;

        if !self.conflicts.is_empty() {
            writeln!(writer, "  <conflicts>")?;
            for entry in &self.conflicts {
                self.write_entry(writer, entry, "    ")?;
            }
            writeln!(writer, "  </conflicts>")?;
        }

        if !self.warnings.is_empty() {
            writeln!(writer, "  <warnings>")?;
            for entry in &self.warnings {
                self.write_entry(writer, entry, "    ")?;
            }
            writeln!(writer, "  </warnings>")?;
        }

        writeln!(writer, "</conflictlist>")?;

        // Print summary to stderr like the Java version
        if !self.conflicts.is_empty() {
            eprintln!("MERGE FAILED: {} conflicts.", self.conflicts.len());
        }
        if !self.warnings.is_empty() {
            eprintln!("Warning: {} conflict warnings.", self.warnings.len());
        }

        Ok(())
    }

    /// Writes a single conflict entry as XML.
    fn write_entry<W: Write>(
        &self,
        writer: &mut W,
        entry: &ConflictEntry,
        indent: &str,
    ) -> std::io::Result<()> {
        let tag = entry.conflict_type.tag_name();

        writeln!(writer, "{}<{}>", indent, tag)?;
        writeln!(writer, "{}  {}", indent, escape_xml(&entry.text))?;

        // Merged tree node
        writeln!(
            writer,
            "{}  <node tree=\"merged\" path=\"{}\" />",
            indent,
            escape_xml(&entry.merge_path)
        )?;

        // Base node
        if let Some(base) = &entry.base {
            let path = get_node_path(base);
            writeln!(
                writer,
                "{}  <node tree=\"base\" path=\"{}\" />",
                indent,
                escape_xml(&path)
            )?;
        }

        // Branch 1 node
        if let Some(b1) = &entry.branch1 {
            let path = get_node_path(b1);
            writeln!(
                writer,
                "{}  <node tree=\"branch1\" path=\"{}\" />",
                indent,
                escape_xml(&path)
            )?;
        }

        // Branch 2 node
        if let Some(b2) = &entry.branch2 {
            let path = get_node_path(b2);
            writeln!(
                writer,
                "{}  <node tree=\"branch2\" path=\"{}\" />",
                indent,
                escape_xml(&path)
            )?;
        }

        writeln!(writer, "{}</{}>", indent, tag)?;
        Ok(())
    }
}

/// Escapes special characters in XML content.
fn escape_xml(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// Gets a path string for a node (for error reporting).
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
            Some(XmlContent::ProcessingInstruction(pi)) => format!("#pi-{}", pi.target()),
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
    fn test_conflict_type_tag_names() {
        assert_eq!(ConflictType::Update.tag_name(), "update");
        assert_eq!(ConflictType::Delete.tag_name(), "delete");
        assert_eq!(ConflictType::Insert.tag_name(), "insert");
        assert_eq!(ConflictType::Move.tag_name(), "move");
    }

    #[test]
    fn test_conflict_log_empty() {
        let log = ConflictLog::new();
        assert!(!log.has_conflicts());
        assert_eq!(log.conflict_count(), 0);
        assert_eq!(log.warning_count(), 0);
    }

    #[test]
    fn test_conflict_log_path() {
        let mut log = ConflictLog::new();
        assert_eq!(log.path_string(), "/");

        log.push_path("root");
        assert_eq!(log.path_string(), "/root");

        log.push_path("child");
        assert_eq!(log.path_string(), "/root/child");

        log.pop_path();
        assert_eq!(log.path_string(), "/root");
    }

    #[test]
    fn test_add_conflict() {
        let mut log = ConflictLog::new();
        log.add_list_conflict(ConflictType::Move, "Test conflict", None, None, None);

        assert!(log.has_conflicts());
        assert_eq!(log.conflict_count(), 1);
        assert_eq!(log.warning_count(), 0);

        let entry = &log.conflicts()[0];
        assert_eq!(entry.conflict_type, ConflictType::Move);
        assert_eq!(entry.text, "Test conflict");
    }

    #[test]
    fn test_add_warning() {
        let mut log = ConflictLog::new();
        log.add_list_warning(ConflictType::Insert, "Test warning", None, None, None);

        assert!(!log.has_conflicts());
        assert_eq!(log.conflict_count(), 0);
        assert_eq!(log.warning_count(), 1);

        let entry = &log.warnings()[0];
        assert_eq!(entry.conflict_type, ConflictType::Insert);
    }
}
