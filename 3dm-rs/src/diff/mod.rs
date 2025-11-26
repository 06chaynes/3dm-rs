//! Diff and Patch algorithms for XML trees.
//!
//! This module provides functionality to generate diffs between matched trees
//! and to apply those diffs to reconstruct modified versions.

mod bfs_index;
mod diff_operation;
mod generator;
mod patch;

pub use bfs_index::BfsIndex;
pub use diff_operation::DiffOperation;
pub use generator::Diff;
pub use patch::Patch;

/// Default namespace for diff tags.
pub const DIFF_NS: &str = "";

/// Tag names for diff operations.
pub const DIFF_COPY_TAG: &str = "copy";
pub const DIFF_INSERT_TAG: &str = "insert";
pub const DIFF_ESC_TAG: &str = "esc";
pub const DIFF_ROOT_TAG: &str = "diff";

/// Attribute names for diff operations.
pub const DIFF_CPYSRC_ATTR: &str = "src";
pub const DIFF_CPYDST_ATTR: &str = "dst";
pub const DIFF_CPYRUN_ATTR: &str = "run";
pub const DIFF_ROOTOP_ATTR: &str = "op";

/// Value for root insert operation.
pub const DIFF_ROOTOP_INS: &str = "insert";
