//! 3DM - Three-way XML Diff and Merge
//!
//! This library provides structure-aware XML merging capabilities.
//! It supports insert, delete, update, move, and copy operations on subtrees.
//!
//! # Overview
//!
//! 3DM (3-way Diff/Merge) is an XML tree differencing and merging tool
//! originally created by Tancred Lindholm as part of his Master's thesis
//! at Helsinki University of Technology (2001).
//!
//! This is a Rust port of the original Java implementation.
//!
//! # Key Features
//!
//! - Structure-aware XML merging (unlike line-based diff/diff3)
//! - Supports insert, delete, update, move, and copy operations on subtrees
//! - No edit history required - only needs the XML files
//!
//! # Example Use Case
//!
//! A document edited by two reviewers - one moves a paragraph, the other
//! fixes a spelling error in that paragraph. 3DM automatically integrates
//! both changes.

pub mod constants;
pub mod diff;
pub mod error;
pub mod matching;
pub mod measure;
pub mod merge;
pub mod node;
pub mod xml;

// Re-export commonly used types
pub use constants::*;
pub use error::{Error, Result};
pub use matching::{DiffMatching, HeuristicMatching, Matching, TriMatching};
pub use measure::Measure;
pub use node::{
    new_base_node, new_branch_node, BaseNode, BranchNode, MatchArea, MatchType, MatchedNodes,
    NodeInner, NodeKind, NodeRef, WeakNodeRef, XmlContent, XmlElement, XmlText,
};
pub use xml::{
    parse_file, parse_str, BaseNodeFactory, BranchNodeFactory, NodeFactory, XmlParser, XmlPrinter,
};

// Re-export merge types
pub use merge::{
    ConflictLog, ConflictType, EditLog, EditType, Merge, MergeEntry, MergeList, MergePair,
    MergePairList, Operation,
};

// Re-export diff types
pub use diff::{BfsIndex, Diff, DiffOperation, Patch};
