//! Tree matching algorithms.
//!
//! This module provides algorithms for establishing correspondences between
//! nodes in base and branch trees. The matching is used by the merge algorithm
//! to identify which nodes have been modified, moved, copied, or deleted.

mod diff;
mod heuristic;
mod tri;

pub use diff::DiffMatching;
pub use heuristic::HeuristicMatching;
pub use tri::TriMatching;

use crate::node::NodeRef;

/// Trait for tree matching algorithms.
///
/// A Matching builds correspondences between a base tree and a branch tree.
/// The actual matchings are stored in the nodes themselves (BaseNode's left/right
/// MatchedNodes and BranchNode's base_match field).
pub trait Matching {
    /// Builds a matching between a base tree and a branch tree.
    ///
    /// After this method returns, the nodes in both trees will have their
    /// matching fields populated.
    fn build_matching(&mut self, base: &NodeRef, branch: &NodeRef);

    /// Gets the children of leaf nodes in a matching subtree.
    ///
    /// Uses the MatchArea tag of nodes to identify the subtree boundaries.
    fn get_area_stop_nodes(&self, stop_nodes: &mut Vec<NodeRef>, node: &NodeRef);

    /// Returns a reference to the base tree root.
    fn base_root(&self) -> Option<&NodeRef>;

    /// Returns a reference to the branch tree root.
    fn branch_root(&self) -> Option<&NodeRef>;
}

/// Constants used by matching algorithms.
pub mod constants {
    /// Threshold for considering a subtree to be copied.
    /// Subtrees smaller than this (in info bytes) are not considered copies.
    pub const COPY_THRESHOLD: i32 = 128;

    /// Info bytes per edge in a matched tree.
    pub const EDGE_BYTES: i32 = 4;

    /// Maximum content dissimilarity when fuzzy matching nodes in DFS search.
    pub const DFS_MATCH_THRESHOLD: f64 = 0.2;

    /// Maximum content dissimilarity when searching for potential matching
    /// subtree roots.
    pub const MAX_FUZZY_MATCH: f64 = 0.2;

    /// Distance value used when both nodes are at the end of their
    /// respective child lists (e.g., both at position 0 for left sibling check).
    pub const END_MATCH: f64 = crate::measure::MAX_DIST;
}

/// A candidate match entry with distance metrics.
#[derive(Debug, Clone)]
pub struct CandidateEntry {
    /// The candidate base node.
    pub candidate: NodeRef,
    /// Content distance between candidate and branch node.
    pub distance: f64,
    /// Minimum of left sibling distance, right sibling distance, and child list distance.
    /// Set to -1.0 if not yet calculated.
    pub left_right_down: f64,
}

impl CandidateEntry {
    /// Creates a new candidate entry.
    pub fn new(candidate: NodeRef, distance: f64, left_right_down: f64) -> Self {
        CandidateEntry {
            candidate,
            distance,
            left_right_down,
        }
    }
}

/// Iterator for traversing a tree in depth-first order.
pub struct DfsTreeIterator {
    /// Stack of (node, next_child_index) pairs for iterating.
    stack: Vec<(NodeRef, usize)>,
}

impl DfsTreeIterator {
    /// Creates a new DFS iterator starting at the given root.
    pub fn new(root: NodeRef) -> Self {
        DfsTreeIterator {
            stack: vec![(root, 0)],
        }
    }
}

impl Iterator for DfsTreeIterator {
    type Item = NodeRef;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, child_idx)) = self.stack.pop() {
            let borrowed = node.borrow();
            let child_count = borrowed.child_count();

            if child_idx == 0 {
                // First visit to this node - return it
                drop(borrowed);
                if child_count > 0 {
                    // Push back with incremented index for later processing
                    self.stack.push((node.clone(), 1));
                    // Push first child
                    let first_child = node.borrow().child(0).cloned();
                    if let Some(child) = first_child {
                        self.stack.push((child, 0));
                    }
                }
                return Some(node);
            } else if child_idx < child_count {
                // Continue with next child
                let next_child = borrowed.child(child_idx).cloned();
                drop(borrowed);
                self.stack.push((node, child_idx + 1));
                if let Some(child) = next_child {
                    self.stack.push((child, 0));
                }
            }
            // If child_idx >= child_count, we're done with this node's children
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_base_node, NodeInner, XmlContent, XmlElement};
    use std::collections::HashMap;

    #[test]
    fn test_dfs_iterator_single_node() {
        let root = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
            HashMap::new(),
        ))));

        let iter = DfsTreeIterator::new(root.clone());
        let nodes: Vec<NodeRef> = iter.collect();

        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].borrow().id(), root.borrow().id());
    }

    #[test]
    fn test_dfs_iterator_tree() {
        // Build tree:
        //       root
        //      /    \
        //     a      b
        //    / \
        //   c   d

        let root = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
            HashMap::new(),
        ))));
        let a = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "a".to_string(),
            HashMap::new(),
        ))));
        let b = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "b".to_string(),
            HashMap::new(),
        ))));
        let c = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "c".to_string(),
            HashMap::new(),
        ))));
        let d = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "d".to_string(),
            HashMap::new(),
        ))));

        NodeInner::add_child_to_ref(&root, a.clone());
        NodeInner::add_child_to_ref(&root, b.clone());
        NodeInner::add_child_to_ref(&a, c.clone());
        NodeInner::add_child_to_ref(&a, d.clone());

        let iter = DfsTreeIterator::new(root.clone());
        let nodes: Vec<NodeRef> = iter.collect();

        // DFS order: root, a, c, d, b
        assert_eq!(nodes.len(), 5);

        // Get element names for easier checking
        let names: Vec<String> = nodes
            .iter()
            .map(|n| {
                let borrowed = n.borrow();
                if let Some(XmlContent::Element(e)) = borrowed.content() {
                    e.qname().to_string()
                } else {
                    String::new()
                }
            })
            .collect();

        assert_eq!(names, vec!["root", "a", "c", "d", "b"]);
    }

    #[test]
    fn test_candidate_entry() {
        let node = new_base_node(None);
        let entry = CandidateEntry::new(node.clone(), 0.5, -1.0);

        assert_eq!(entry.distance, 0.5);
        assert_eq!(entry.left_right_down, -1.0);
    }
}
