//! Diff generation algorithm.
//!
//! Produces an XML diff document that encodes the transformations needed
//! to convert the base tree into the branch tree.

use std::io::Write;

use crate::matching::Matching;
use crate::node::{BranchNode, NodeRef, XmlContent};

use super::bfs_index::BfsIndex;
use super::diff_operation::{DiffOpType, DiffOperation};
use super::{
    DIFF_COPY_TAG, DIFF_CPYDST_ATTR, DIFF_CPYRUN_ATTR, DIFF_CPYSRC_ATTR, DIFF_ESC_TAG,
    DIFF_INSERT_TAG, DIFF_ROOTOP_ATTR, DIFF_ROOTOP_INS, DIFF_ROOT_TAG,
};

/// Sequence for run-length encoding of consecutive copies.
struct Sequence {
    /// Source node ID for start of sequence.
    src: Option<u64>,
    /// Destination node ID.
    dst: Option<u64>,
    /// Tail node ID (last in sequence).
    tail: Option<u64>,
    /// Number of consecutive nodes.
    run: i64,
}

impl Sequence {
    fn new() -> Self {
        Sequence {
            src: None,
            dst: None,
            tail: None,
            run: -1,
        }
    }

    fn set_empty(&mut self) {
        self.run = -1;
    }

    fn is_empty(&self) -> bool {
        self.run == -1
    }

    fn init(&mut self, src: u64, dst: Option<u64>) {
        self.src = Some(src);
        self.tail = Some(src);
        self.dst = dst;
        self.run = 1;
    }

    fn append(&mut self, src: u64) {
        self.run += 1;
        self.tail = Some(src);
    }
}

/// Diff generator for matched trees.
pub struct Diff<'a> {
    /// The matching between base and branch trees.
    matching: &'a dyn Matching,
    /// BFS index for the base tree.
    index: BfsIndex,
    /// Current indentation level for formatted output.
    indent: std::cell::Cell<usize>,
}

impl<'a> Diff<'a> {
    /// Creates a new diff generator.
    pub fn new(matching: &'a dyn Matching) -> Option<Self> {
        let base_root = matching.base_root()?;
        let index = BfsIndex::new(base_root);

        Some(Diff {
            matching,
            index,
            indent: std::cell::Cell::new(0),
        })
    }

    /// Creates a diff generator with a custom index.
    pub fn with_index(matching: &'a dyn Matching, index: BfsIndex) -> Self {
        Diff {
            matching,
            index,
            indent: std::cell::Cell::new(0),
        }
    }

    /// Generates the diff and writes it to the given writer.
    pub fn diff<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        if let Some(branch_root) = self.matching.branch_root() {
            self.diff_from(writer, branch_root)
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "No branch root",
            ))
        }
    }

    /// Generates diff starting from a specific branch node.
    fn diff_from<W: Write>(&self, writer: &mut W, branch_root: &NodeRef) -> std::io::Result<()> {
        let root_has_match = BranchNode::base_match(branch_root).is_some();

        writeln!(writer, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>")?;

        if root_has_match {
            // Root matches - use copy operation
            let stop_nodes = self.get_stop_nodes(branch_root);
            let op = DiffOperation::root_copy();
            self.write_op_open(writer, &op)?;
            self.write_copy(writer, &stop_nodes)?;
            self.write_op_close(writer, &op)?;
        } else {
            // Root doesn't match - insert operation
            let op = DiffOperation::root_insert();
            self.write_op_open(writer, &op)?;
            self.write_insert(writer, branch_root)?;
            self.write_op_close(writer, &op)?;
        }

        Ok(())
    }

    /// Gets stop nodes for a matched subtree.
    fn get_stop_nodes(&self, node: &NodeRef) -> Vec<NodeRef> {
        let mut stop_nodes = Vec::new();
        self.matching.get_area_stop_nodes(&mut stop_nodes, node);
        stop_nodes
    }

    /// Writes the copy operations for the given stop nodes.
    fn write_copy<W: Write>(&self, writer: &mut W, stop_nodes: &[NodeRef]) -> std::io::Result<()> {
        let mut seq = Sequence::new();

        for stop_node in stop_nodes {
            let dst = BranchNode::base_match(stop_node).and_then(|n| self.index.get_id(&n));

            if !self.emit_child_list(writer, &mut seq, stop_node, dst, false)? {
                // Leaf node (e.g. PI, comment, text) with no children
                let op = DiffOperation::insert(dst);
                self.write_op_open(writer, &op)?;
                self.write_content_open(writer, stop_node)?;
                self.write_content_close(writer, stop_node)?;
                self.write_op_close(writer, &op)?;
            }
        }

        Ok(())
    }

    /// Writes an insert operation for a branch node.
    fn write_insert<W: Write>(&self, writer: &mut W, branch: &NodeRef) -> std::io::Result<()> {
        let mut seq = Sequence::new();
        self.write_content_open(writer, branch)?;
        self.emit_child_list(writer, &mut seq, branch, None, true)?;
        self.write_content_close(writer, branch)?;
        Ok(())
    }

    /// Emits the child list with run-length encoding for copies.
    fn emit_child_list<W: Write>(
        &self,
        writer: &mut W,
        seq: &mut Sequence,
        parent: &NodeRef,
        dst: Option<u64>,
        ins_mode: bool,
    ) -> std::io::Result<bool> {
        let children: Vec<_> = parent.borrow().children().to_vec();
        let child_count = children.len();

        for (ic, child) in children.iter().enumerate() {
            let last_stop_node = ic == child_count - 1;
            let base_match = BranchNode::base_match(child);

            if let Some(ref base) = base_match {
                // Child has a base match - potential copy
                let child_stop_nodes = self.get_stop_nodes(child);
                let src = self.index.get_id(base);

                if let Some(src_id) = src {
                    if child_stop_nodes.is_empty() && !last_stop_node {
                        // Can potentially extend sequence
                        if seq.is_empty() {
                            seq.init(src_id, dst);
                            continue;
                        } else if self.sequence_appends(seq, src_id, dst) {
                            seq.append(src_id);
                            continue;
                        }
                    }

                    // Did not append to sequence (or at last stop node) => emit sequence
                    if !self.sequence_appends(seq, src_id, dst) {
                        // Current does not append to prev seq -> output prev seq + new in separate tags
                        if !seq.is_empty() {
                            let op = DiffOperation::copy(seq.src.unwrap(), seq.dst, seq.run as u64);
                            self.write_op_open(writer, &op)?;
                            self.write_op_close(writer, &op)?;
                        }

                        if !child_stop_nodes.is_empty() || last_stop_node {
                            let op = DiffOperation::copy(src_id, dst, 1);
                            self.write_op_open(writer, &op)?;
                            self.write_copy(writer, &child_stop_nodes)?;
                            self.write_op_close(writer, &op)?;
                            seq.set_empty();
                        } else {
                            seq.init(src_id, dst);
                        }
                    } else {
                        // Appends to open sequence (other reason for seq break)
                        seq.append(src_id);
                        let op = DiffOperation::copy(seq.src.unwrap(), seq.dst, seq.run as u64);
                        self.write_op_open(writer, &op)?;
                        self.write_copy(writer, &child_stop_nodes)?;
                        self.write_op_close(writer, &op)?;
                        seq.set_empty();
                    }
                }
            } else {
                // No base match - insert
                if !seq.is_empty() {
                    let op = DiffOperation::copy(seq.src.unwrap(), seq.dst, seq.run as u64);
                    self.write_op_open(writer, &op)?;
                    self.write_op_close(writer, &op)?;
                    seq.set_empty();
                }

                if !ins_mode {
                    // Check if we need to open an insert tag (SHORTINS optimization)
                    let prev_has_match =
                        ic > 0 && BranchNode::base_match(&children[ic - 1]).is_some();
                    if ic == 0 || prev_has_match {
                        let op = DiffOperation::insert(dst);
                        self.write_op_open(writer, &op)?;
                    }
                }

                self.write_insert(writer, child)?;

                if !ins_mode {
                    // Check if we need to close the insert tag (SHORTINS optimization)
                    let next_has_match = !last_stop_node
                        && ic + 1 < child_count
                        && BranchNode::base_match(&children[ic + 1]).is_some();
                    if last_stop_node || next_has_match {
                        let op = DiffOperation::insert(None);
                        self.write_op_close(writer, &op)?;
                    }
                }
            }
        }

        Ok(!children.is_empty())
    }

    /// Checks if a source ID appends to the current sequence.
    fn sequence_appends(&self, seq: &Sequence, src: u64, dst: Option<u64>) -> bool {
        if seq.is_empty() {
            return false;
        }
        if dst != seq.dst {
            return false;
        }
        match (seq.tail, self.index.lookup(seq.tail.unwrap())) {
            (Some(_), Some(tail_node)) => {
                if let Some(next_node) = self.index.lookup(src) {
                    self.index.appends(&tail_node, &next_node)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Writes the opening tag for a diff operation.
    fn write_op_open<W: Write>(&self, writer: &mut W, op: &DiffOperation) -> std::io::Result<()> {
        let indent_str = Self::indent_str_for(self.indent.get());
        match op.op_type {
            DiffOpType::RootCopy => {
                writeln!(writer, "{}<{}>", indent_str, DIFF_ROOT_TAG)?;
                self.indent.set(self.indent.get() + 1);
            }
            DiffOpType::RootInsert => {
                writeln!(
                    writer,
                    "{}<{} {}=\"{}\">",
                    indent_str, DIFF_ROOT_TAG, DIFF_ROOTOP_ATTR, DIFF_ROOTOP_INS
                )?;
                self.indent.set(self.indent.get() + 1);
            }
            DiffOpType::Copy => {
                write!(writer, "{}<{}", indent_str, DIFF_COPY_TAG)?;
                if let Some(src) = op.source {
                    write!(writer, " {}=\"{}\"", DIFF_CPYSRC_ATTR, src)?;
                }
                if let Some(dst) = op.destination {
                    write!(writer, " {}=\"{}\"", DIFF_CPYDST_ATTR, dst)?;
                }
                if let Some(run) = op.run {
                    if run > 1 {
                        write!(writer, " {}=\"{}\"", DIFF_CPYRUN_ATTR, run)?;
                    }
                }
                writeln!(writer, ">")?;
                self.indent.set(self.indent.get() + 1);
            }
            DiffOpType::Insert => {
                write!(writer, "{}<{}", indent_str, DIFF_INSERT_TAG)?;
                if let Some(dst) = op.destination {
                    write!(writer, " {}=\"{}\"", DIFF_CPYDST_ATTR, dst)?;
                }
                writeln!(writer, ">")?;
                self.indent.set(self.indent.get() + 1);
            }
        }
        Ok(())
    }

    /// Writes the closing tag for a diff operation.
    fn write_op_close<W: Write>(&self, writer: &mut W, op: &DiffOperation) -> std::io::Result<()> {
        self.indent.set(self.indent.get() - 1);
        let indent_str = Self::indent_str_for(self.indent.get());
        match op.op_type {
            DiffOpType::RootCopy | DiffOpType::RootInsert => {
                writeln!(writer, "{}</{}>", indent_str, DIFF_ROOT_TAG)?;
            }
            DiffOpType::Copy => {
                writeln!(writer, "{}</{}>", indent_str, DIFF_COPY_TAG)?;
            }
            DiffOpType::Insert => {
                writeln!(writer, "{}</{}>", indent_str, DIFF_INSERT_TAG)?;
            }
        }
        Ok(())
    }

    /// Checks if an element name conflicts with diff reserved tags.
    fn needs_escape(qname: &str) -> bool {
        qname == DIFF_COPY_TAG || qname == DIFF_INSERT_TAG || qname == DIFF_ESC_TAG
    }

    /// Writes the opening content for a node.
    fn write_content_open<W: Write>(&self, writer: &mut W, node: &NodeRef) -> std::io::Result<()> {
        let borrowed = node.borrow();
        match borrowed.content() {
            Some(XmlContent::Text(text)) => {
                // Convert char slice to String
                let text_str: String = text.text().iter().collect();
                write!(
                    writer,
                    "{}{}",
                    Self::indent_str_for(self.indent.get()),
                    escape_xml(&text_str)
                )?;
            }
            Some(XmlContent::Comment(comment)) => {
                // Output comment
                let comment_text: String = comment.text().iter().collect();
                writeln!(
                    writer,
                    "{}<!-- {} -->",
                    Self::indent_str_for(self.indent.get()),
                    comment_text
                )?;
            }
            Some(XmlContent::ProcessingInstruction(pi)) => {
                // Output processing instruction
                if pi.content().is_empty() {
                    writeln!(
                        writer,
                        "{}<?{}?>",
                        Self::indent_str_for(self.indent.get()),
                        pi.target()
                    )?;
                } else {
                    writeln!(
                        writer,
                        "{}<?{} {}?>",
                        Self::indent_str_for(self.indent.get()),
                        pi.target(),
                        pi.content()
                    )?;
                }
            }
            Some(XmlContent::Element(elem)) => {
                // Check if element name conflicts with diff reserved tags
                let needs_esc = Self::needs_escape(elem.qname());
                if needs_esc {
                    writeln!(
                        writer,
                        "{}<{}>",
                        Self::indent_str_for(self.indent.get()),
                        DIFF_ESC_TAG
                    )?;
                    self.indent.set(self.indent.get() + 1);
                }

                write!(
                    writer,
                    "{}<{}",
                    Self::indent_str_for(self.indent.get()),
                    elem.qname()
                )?;
                // Namespace declarations (sorted for deterministic output)
                let mut ns_prefixes: Vec<_> = elem.namespace_decls().keys().collect();
                ns_prefixes.sort();
                for prefix in ns_prefixes {
                    if let Some(uri) = elem.namespace_decls().get(prefix) {
                        if prefix.is_empty() {
                            write!(writer, " xmlns=\"{}\"", escape_xml_attr(uri))?;
                        } else {
                            write!(writer, " xmlns:{}=\"{}\"", prefix, escape_xml_attr(uri))?;
                        }
                    }
                }
                // Attributes (sorted for deterministic output)
                let mut attr_names: Vec<_> = elem.attributes().keys().collect();
                attr_names.sort();
                for name in attr_names {
                    if let Some(value) = elem.attributes().get(name) {
                        write!(writer, " {}=\"{}\"", name, escape_xml_attr(value))?;
                    }
                }
                writeln!(writer, ">")?;
                self.indent.set(self.indent.get() + 1);
            }
            None => {}
        }
        Ok(())
    }

    /// Writes the closing content for a node.
    fn write_content_close<W: Write>(&self, writer: &mut W, node: &NodeRef) -> std::io::Result<()> {
        let borrowed = node.borrow();
        if let Some(XmlContent::Element(elem)) = borrowed.content() {
            self.indent.set(self.indent.get() - 1);
            writeln!(
                writer,
                "{}</{}>",
                Self::indent_str_for(self.indent.get()),
                elem.qname()
            )?;

            // Close escape wrapper if element name was reserved
            if Self::needs_escape(elem.qname()) {
                self.indent.set(self.indent.get() - 1);
                writeln!(
                    writer,
                    "{}</{}>",
                    Self::indent_str_for(self.indent.get()),
                    DIFF_ESC_TAG
                )?;
            }
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
    use crate::matching::HeuristicMatching;
    use crate::node::{
        new_base_node, new_branch_node, NodeInner, XmlContent, XmlElement, XmlProcessingInstruction,
    };
    use std::collections::HashMap;

    #[test]
    fn test_escape_xml() {
        assert_eq!(escape_xml("hello"), "hello");
        assert_eq!(escape_xml("<test>"), "&lt;test&gt;");
        assert_eq!(escape_xml("a & b"), "a &amp; b");
    }

    #[test]
    fn test_escape_xml_attr() {
        assert_eq!(escape_xml_attr("hello"), "hello");
        assert_eq!(escape_xml_attr("say \"hi\""), "say &quot;hi&quot;");
    }

    #[test]
    fn test_diff_identical_trees() {
        // Create identical base and branch trees
        let base = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
            HashMap::new(),
        ))));
        let base_child = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "child".to_string(),
            HashMap::new(),
        ))));
        NodeInner::add_child_to_ref(&base, base_child);

        let branch = new_branch_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
            HashMap::new(),
        ))));
        let branch_child = new_branch_node(Some(XmlContent::Element(XmlElement::new(
            "child".to_string(),
            HashMap::new(),
        ))));
        NodeInner::add_child_to_ref(&branch, branch_child);

        // Create matching
        let mut matching = HeuristicMatching::new();
        matching.build_matching(&base, &branch);

        // Generate diff
        if let Some(diff) = Diff::new(&matching) {
            let mut output = Vec::new();
            diff.diff(&mut output).unwrap();

            let result = String::from_utf8(output).unwrap();
            assert!(result.contains("<diff>"));
            assert!(result.contains("</diff>"));
        }
    }

    #[test]
    fn test_diff_pi_insertion() {
        // Base: $ROOT$ -> root element (no PI)
        let base = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "$ROOT$".to_string(),
            HashMap::new(),
        ))));
        let base_root = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
            HashMap::new(),
        ))));
        NodeInner::add_child_to_ref(&base, base_root);

        // Branch: $ROOT$ -> PI + root element
        let branch = new_branch_node(Some(XmlContent::Element(XmlElement::new(
            "$ROOT$".to_string(),
            HashMap::new(),
        ))));
        let pi = new_branch_node(Some(XmlContent::ProcessingInstruction(
            XmlProcessingInstruction::new("my-pi", "some data"),
        )));
        NodeInner::add_child_to_ref(&branch, pi);
        let branch_root = new_branch_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
            HashMap::new(),
        ))));
        NodeInner::add_child_to_ref(&branch, branch_root);

        let mut matching = HeuristicMatching::new();
        matching.build_matching(&base, &branch);

        if let Some(diff) = Diff::new(&matching) {
            let mut output = Vec::new();
            diff.diff(&mut output).unwrap();

            let result = String::from_utf8(output).unwrap();
            assert!(
                result.contains("<?my-pi some data?>"),
                "Diff output should contain PI content, got: {}",
                result
            );
        }
    }
}
