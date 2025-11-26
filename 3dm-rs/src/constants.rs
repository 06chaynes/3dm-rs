//! Constants used throughout 3DM.
//!
//! These constants mirror those in the Java Measure class.

/// Maximum distance value. Distance is normalized between 0 and MAX_DIST.
pub const MAX_DIST: f64 = 1.0;

/// Distance to return by child_list_distance if both nodes have 0 children.
pub const ZERO_CHILDREN_MATCH: f64 = 1.0;

/// Info bytes in an element name ($c_e$ in thesis).
pub const ELEMENT_NAME_INFO: i32 = 1;

/// Info bytes in the presence of an attribute ($c_a$ in thesis).
pub const ATTR_INFO: i32 = 2;

/// Attribute values less than this have an info size of 1 ($c_v$ in thesis).
pub const ATTR_VALUE_THRESHOLD: i32 = 5;

/// Text nodes shorter than this have an info size of 1 ($c_t$ in thesis).
pub const TEXT_THRESHOLD: i32 = 5;

/// Penalty term ($c_p$ in thesis).
pub const PENALTY_C: i32 = 20;

/// Minimum info bytes for copy detection (from HeuristicMatching).
pub const COPY_THRESHOLD: i32 = 128;

/// Max distance for fuzzy DFS matching.
pub const DFS_MATCH_THRESHOLD: f64 = 0.2;

/// Max distance for candidate fuzzy matching.
pub const MAX_FUZZY_MATCH: f64 = 0.2;

/// Info bytes per tree edge.
pub const EDGE_BYTES: i32 = 4;
