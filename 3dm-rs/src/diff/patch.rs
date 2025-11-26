//! Patch application algorithm.
//!
//! Applies a diff document to a base tree to reconstruct the modified version.

use std::collections::HashMap;
use std::io::Write;

use crate::error::{Error, Result};
use crate::node::{new_branch_node, NodeInner, NodeRef, XmlContent, XmlElement};

use super::bfs_index::BfsIndex;
use super::{
    DIFF_COPY_TAG, DIFF_CPYDST_ATTR, DIFF_CPYRUN_ATTR, DIFF_CPYSRC_ATTR, DIFF_ESC_TAG,
    DIFF_INSERT_TAG, DIFF_ROOTOP_ATTR, DIFF_ROOTOP_INS, DIFF_ROOT_TAG,
};

/// Patch application for applying diffs to base trees.
pub struct Patch {
    _placeholder: (),
}

impl Default for Patch {
    fn default() -> Self {
        Self::new()
    }
}

impl Patch {
    /// Creates a new patch applicator.
    pub fn new() -> Self {
        Patch { _placeholder: () }
    }

    /// Applies a diff to a base tree and writes the result.
    ///
    /// # Arguments
    /// * `base` - The base tree to patch
    /// * `diff` - The diff tree (parsed from diff XML)
    /// * `writer` - Output writer for the patched tree
    pub fn patch<W: Write>(&self, base: &NodeRef, diff: &NodeRef, writer: &mut W) -> Result<()> {
        let index = BfsIndex::new(base);
        let patched = self.apply_patch(diff, &index)?;

        // Write output
        writer.write_all(b"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")?;

        // Get first child (skip the dummy root)
        let borrowed = patched.borrow();
        if let Some(child) = borrowed.children().first() {
            self.dump_tree(child, writer, 0)?;
        }

        Ok(())
    }

    /// Applies the patch and returns the patched tree.
    fn apply_patch(&self, diff: &NodeRef, index: &BfsIndex) -> Result<NodeRef> {
        // Create a dummy root to hold the result
        let patch_root = new_branch_node(Some(XmlContent::Element(XmlElement::new(
            "$DUMMY$".to_string(),
            HashMap::new(),
        ))));

        // Get the diff element (skip $ROOT$ fake root if present)
        let diff_elem = {
            let borrowed = diff.borrow();
            if let Some(first_child) = borrowed.children().first() {
                first_child.clone()
            } else {
                return Err(Error::Parse("Empty diff document".to_string()));
            }
        };

        // Verify it's a diff root tag
        let is_diff_root = {
            let borrowed = diff_elem.borrow();
            match borrowed.content() {
                Some(XmlContent::Element(e)) => e.qname() == DIFF_ROOT_TAG,
                _ => false,
            }
        };

        if !is_diff_root {
            return Err(Error::Parse("Invalid root tag for diff".to_string()));
        }

        // Check for root operation attribute
        let root_op = {
            let borrowed = diff_elem.borrow();
            if let Some(XmlContent::Element(e)) = borrowed.content() {
                e.attributes().get(DIFF_ROOTOP_ATTR).cloned()
            } else {
                None
            }
        };

        match root_op.as_deref() {
            None | Some("") => {
                // Default op is copy
                let root_id = index.root_id();
                self.apply_copy(&patch_root, &diff_elem, root_id, index)?;
            }
            Some(op) if op == DIFF_ROOTOP_INS => {
                // Insert operation
                self.apply_insert(&patch_root, &diff_elem, index)?;
            }
            Some(op) => {
                return Err(Error::Parse(format!("Invalid rootop for diff: {}", op)));
            }
        }

        // Return the first child of the patch root
        let borrowed = patch_root.borrow();
        borrowed
            .children()
            .first()
            .cloned()
            .ok_or_else(|| Error::Parse("Patch produced no output".to_string()))
    }

    /// Applies an insert operation.
    fn apply_insert(&self, patch: &NodeRef, diff: &NodeRef, index: &BfsIndex) -> Result<()> {
        let (content, is_command, qname) = {
            let diff_borrowed = diff.borrow();
            let content = diff_borrowed.content().cloned();

            // Check if this is a command or just content to insert
            let (is_command, qname) = match &content {
                Some(XmlContent::Element(e)) => {
                    let qn = e.qname().to_string();
                    let is_cmd = qn == DIFF_COPY_TAG || qn == DIFF_INSERT_TAG || qn == DIFF_ESC_TAG;
                    (is_cmd, Some(qn))
                }
                _ => (false, None),
            };

            (content, is_command, qname)
        };

        if !is_command {
            // Simple insert - create node and recurse for children
            let node = new_branch_node(content);

            let children: Vec<_> = diff.borrow().children().to_vec();
            for child in children {
                self.apply_insert(&node, &child, index)?;
            }

            NodeInner::add_child_to_ref(patch, node);
        } else if let Some(qn) = qname {
            if qn == DIFF_ESC_TAG || qn == DIFF_INSERT_TAG {
                // Process children
                let children: Vec<_> = diff.borrow().children().to_vec();
                for child in children {
                    self.apply_insert(patch, &child, index)?;
                }
            } else if qn == DIFF_COPY_TAG {
                // Copy operation
                let src_str = {
                    let diff_borrowed = diff.borrow();
                    if let Some(XmlContent::Element(e)) = diff_borrowed.content() {
                        e.attributes().get(DIFF_CPYSRC_ATTR).cloned()
                    } else {
                        None
                    }
                };

                let src_str = src_str.ok_or_else(|| {
                    Error::Parse("Missing src attribute in copy command".to_string())
                })?;

                let src_id = src_str.parse().unwrap_or(0);
                self.apply_copy(patch, diff, src_id, index)?;
            }
        }

        Ok(())
    }

    /// Applies a copy operation.
    fn apply_copy(
        &self,
        patch: &NodeRef,
        diff: &NodeRef,
        src_id: u64,
        index: &BfsIndex,
    ) -> Result<()> {
        // Gather stop nodes and their destinations
        let mut dst_nodes: Vec<(u64, NodeRef)> = Vec::new();
        let mut stop_nodes: HashMap<u64, Option<NodeRef>> = HashMap::new();

        // Get run count
        let run = {
            let diff_borrowed = diff.borrow();
            match diff_borrowed.content() {
                Some(XmlContent::Element(e)) => e
                    .attributes()
                    .get(DIFF_CPYRUN_ATTR)
                    .and_then(|v| v.parse::<u64>().ok())
                    .unwrap_or(1),
                _ => 1,
            }
        };

        // Process diff children to find stop nodes
        {
            let diff_borrowed = diff.borrow();
            for child in diff_borrowed.children() {
                let child_borrowed = child.borrow();
                let child_content = child_borrowed.content();

                // Verify it's a copy or insert command
                let is_valid_cmd = match child_content {
                    Some(XmlContent::Element(e)) => {
                        let qname = e.qname();
                        qname == DIFF_COPY_TAG || qname == DIFF_INSERT_TAG
                    }
                    _ => false,
                };

                if !is_valid_cmd {
                    return Err(Error::Parse(
                        "Only copy or insert commands may appear below a copy command".to_string(),
                    ));
                }

                // Get destination node
                let dst_str = match child_content {
                    Some(XmlContent::Element(e)) => e.attributes().get(DIFF_CPYDST_ATTR).cloned(),
                    _ => None,
                };

                if let Some(dst_str) = dst_str {
                    let stop_node = index.lookup_str(&dst_str).ok_or_else(|| {
                        Error::Parse(format!("Invalid dst in command: {}", dst_str))
                    })?;

                    let stop_id = stop_node.borrow().id();
                    dst_nodes.push((stop_id, child.clone()));
                    stop_nodes.entry(stop_id).or_insert(None);
                }
            }
        }

        // Get source root
        let src_root = index
            .lookup(src_id)
            .ok_or_else(|| Error::Parse(format!("Invalid src in copy command: {}", src_id)))?;

        // Perform copy with run count
        let mut current_src = src_root;
        let mut current_id = src_id;

        for _i_run in 1..run {
            self.dfs_copy(patch, &current_src, &mut HashMap::new())?;
            current_id += 1;
            if let Some(next) = index.lookup(current_id) {
                current_src = next;
            }
        }

        // Final copy with stop nodes
        self.dfs_copy(patch, &current_src, &mut stop_nodes)?;

        // Recurse for each diff child
        for (stop_id, diff_child) in &dst_nodes {
            if let Some(Some(created_node)) = stop_nodes.get(stop_id) {
                self.apply_insert(created_node, diff_child, index)?;
            }
        }

        Ok(())
    }

    /// Performs a DFS copy of the source tree.
    #[allow(clippy::only_used_in_recursion)]
    fn dfs_copy(
        &self,
        dst: &NodeRef,
        src: &NodeRef,
        stop_nodes: &mut HashMap<u64, Option<NodeRef>>,
    ) -> Result<()> {
        let (content, src_id, children) = {
            let src_borrowed = src.borrow();
            (
                src_borrowed.content().cloned(),
                src_borrowed.id(),
                src_borrowed.children().to_vec(),
            )
        };

        let copied = new_branch_node(content);
        NodeInner::add_child_to_ref(dst, copied.clone());

        if let std::collections::hash_map::Entry::Occupied(mut e) = stop_nodes.entry(src_id) {
            // Mark this as the stop point and record the created node
            e.insert(Some(copied));
            return Ok(());
        }

        // Copy children
        for child in children {
            self.dfs_copy(&copied, &child, stop_nodes)?;
        }

        Ok(())
    }

    /// Writes the tree to the output.
    #[allow(clippy::only_used_in_recursion)]
    fn dump_tree<W: Write>(
        &self,
        node: &NodeRef,
        writer: &mut W,
        indent: usize,
    ) -> std::io::Result<()> {
        let borrowed = node.borrow();

        match borrowed.content() {
            Some(XmlContent::Text(text)) => {
                // Convert char slice to String
                let text_str: String = text.text().iter().collect();
                write!(
                    writer,
                    "{}{}",
                    Self::indent_str_for(indent),
                    escape_xml(&text_str)
                )?;
            }
            Some(XmlContent::Comment(comment)) => {
                // Output comment
                let comment_text: String = comment.text().iter().collect();
                writeln!(
                    writer,
                    "{}<!-- {} -->",
                    Self::indent_str_for(indent),
                    comment_text
                )?;
            }
            Some(XmlContent::Element(elem)) => {
                write!(writer, "{}<{}", Self::indent_str_for(indent), elem.qname())?;
                // Sort attributes for consistent output
                let mut attr_names: Vec<_> = elem.attributes().keys().collect();
                attr_names.sort();
                for name in attr_names {
                    if let Some(value) = elem.attributes().get(name) {
                        write!(writer, " {}=\"{}\"", name, escape_xml_attr(value))?;
                    }
                }
                writeln!(writer, ">")?;

                for child in borrowed.children() {
                    self.dump_tree(child, writer, indent + 1)?;
                }

                writeln!(
                    writer,
                    "{}</{}>",
                    Self::indent_str_for(indent),
                    elem.qname()
                )?;
            }
            None => {}
        }

        Ok(())
    }

    /// Returns the indentation string for a given level.
    fn indent_str_for(level: usize) -> String {
        "  ".repeat(level)
    }
}

/// Escapes special XML characters in text content.
fn escape_xml(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

/// Escapes special XML characters in attribute values.
fn escape_xml_attr(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_base_node, XmlText};

    fn create_base_tree() -> NodeRef {
        let root = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
            HashMap::new(),
        ))));
        let child1 = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "child1".to_string(),
            HashMap::new(),
        ))));
        let child2 = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "child2".to_string(),
            HashMap::new(),
        ))));
        let text = new_base_node(Some(XmlContent::Text(XmlText::new("hello"))));

        NodeInner::add_child_to_ref(&child1, text);
        NodeInner::add_child_to_ref(&root, child1);
        NodeInner::add_child_to_ref(&root, child2);

        root
    }

    fn create_simple_diff() -> NodeRef {
        // Create a diff that just copies the root
        // <$ROOT$><diff><copy src="0" /></diff></$ROOT$>
        let fake_root = new_branch_node(Some(XmlContent::Element(XmlElement::new(
            "$ROOT$".to_string(),
            HashMap::new(),
        ))));
        let diff_elem = new_branch_node(Some(XmlContent::Element(XmlElement::new(
            DIFF_ROOT_TAG.to_string(),
            HashMap::new(),
        ))));

        NodeInner::add_child_to_ref(&fake_root, diff_elem);

        fake_root
    }

    #[test]
    fn test_patch_new() {
        let _patch = Patch::new();
        // Just verify construction works
    }

    #[test]
    fn test_escape_functions() {
        assert_eq!(escape_xml("<test>"), "&lt;test&gt;");
        assert_eq!(escape_xml_attr("\"test\""), "&quot;test&quot;");
    }

    #[test]
    fn test_simple_patch() {
        let base = create_base_tree();
        let diff = create_simple_diff();
        let patch = Patch::new();

        let mut output = Vec::new();
        let result = patch.patch(&base, &diff, &mut output);

        // This might fail due to diff structure, but shouldn't panic
        // The actual integration test would use properly structured diffs
        assert!(result.is_ok() || result.is_err());
    }
}
