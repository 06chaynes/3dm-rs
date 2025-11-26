//! XML parsing and output.
//!
//! This module provides XML parsing and printing functionality that matches
//! the Java implementation's behavior for byte-for-byte compatibility.

mod parser;
mod printer;

pub use parser::{parse_file, parse_str, XmlParser};
pub use printer::{print_to_string, print_to_string_pretty, XmlPrinter, XmlPrinterOptions};

use crate::node::{NodeRef, XmlContent};

/// Factory trait for creating nodes during parsing.
///
/// This allows the parser to create either BaseNode or BranchNode trees
/// depending on the context.
pub trait NodeFactory {
    /// Creates a new node with the given content.
    fn make_node(&self, content: XmlContent) -> NodeRef;
}

/// Factory that creates base nodes.
pub struct BaseNodeFactory;

impl NodeFactory for BaseNodeFactory {
    fn make_node(&self, content: XmlContent) -> NodeRef {
        crate::node::new_base_node(Some(content))
    }
}

/// Factory that creates branch nodes.
pub struct BranchNodeFactory;

impl NodeFactory for BranchNodeFactory {
    fn make_node(&self, content: XmlContent) -> NodeRef {
        crate::node::new_branch_node(Some(content))
    }
}
