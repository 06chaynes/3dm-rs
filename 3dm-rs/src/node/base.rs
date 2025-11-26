//! Base node helper functions.
//!
//! This module provides helper functions for working with base nodes.
//! Base nodes are nodes in the base tree that are matched to two branch trees
//! (left and right).

use std::cell::RefCell;
use std::rc::Rc;

use super::{MatchedNodes, NodeKind, NodeRef};

/// Helper functions for base nodes.
pub struct BaseNode;

impl BaseNode {
    /// Returns the left MatchedNodes for a base node.
    ///
    /// # Panics
    /// Panics if the node is not a base node.
    pub fn left(node: &NodeRef) -> Rc<RefCell<MatchedNodes>> {
        let borrowed = node.borrow();
        match &borrowed.kind {
            NodeKind::Base { left, .. } => Rc::clone(left),
            NodeKind::Branch { .. } => panic!("left() called on branch node"),
        }
    }

    /// Returns the right MatchedNodes for a base node.
    ///
    /// # Panics
    /// Panics if the node is not a base node.
    pub fn right(node: &NodeRef) -> Rc<RefCell<MatchedNodes>> {
        let borrowed = node.borrow();
        match &borrowed.kind {
            NodeKind::Base { right, .. } => Rc::clone(right),
            NodeKind::Branch { .. } => panic!("right() called on branch node"),
        }
    }

    /// Swaps the left and right matchings.
    ///
    /// # Panics
    /// Panics if the node is not a base node.
    pub fn swap_left_right_matchings(node: &NodeRef) {
        let mut borrowed = node.borrow_mut();
        match &mut borrowed.kind {
            NodeKind::Base { left, right } => {
                std::mem::swap(left, right);
            }
            NodeKind::Branch { .. } => panic!("swap_left_right_matchings() called on branch node"),
        }
    }

    /// Gets the child at the given index, asserting it's a base node.
    ///
    /// # Panics
    /// Panics if the index is out of bounds or if the child is not a base node.
    pub fn child(node: &NodeRef, index: usize) -> NodeRef {
        let borrowed = node.borrow();
        let child = borrowed
            .children()
            .get(index)
            .expect("child index out of bounds")
            .clone();
        assert!(child.borrow().is_base(), "child is not a base node");
        child
    }

    /// Gets the parent, asserting it's a base node.
    ///
    /// Returns None if there is no parent.
    ///
    /// # Panics
    /// Panics if the parent exists but is not a base node.
    pub fn parent(node: &NodeRef) -> Option<NodeRef> {
        let borrowed = node.borrow();
        borrowed.parent().upgrade().inspect(|p| {
            assert!(p.borrow().is_base(), "parent is not a base node");
        })
    }

    /// Checks if the given node is a base node.
    pub fn is_base(node: &NodeRef) -> bool {
        node.borrow().is_base()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_base_node, new_branch_node, NodeInner};

    #[test]
    fn test_base_left_right() {
        let base = new_base_node(None);

        // Should not panic
        let _left = BaseNode::left(&base);
        let _right = BaseNode::right(&base);
    }

    #[test]
    #[should_panic(expected = "left() called on branch node")]
    fn test_left_on_branch_panics() {
        let branch = new_branch_node(None);
        let _left = BaseNode::left(&branch);
    }

    #[test]
    fn test_swap_matchings() {
        let base = new_base_node(None);
        let branch = new_branch_node(None);

        // Add branch to left matches
        BaseNode::left(&base).borrow_mut().add_match(branch.clone());

        assert_eq!(BaseNode::left(&base).borrow().match_count(), 1);
        assert_eq!(BaseNode::right(&base).borrow().match_count(), 0);

        // Swap
        BaseNode::swap_left_right_matchings(&base);

        assert_eq!(BaseNode::left(&base).borrow().match_count(), 0);
        assert_eq!(BaseNode::right(&base).borrow().match_count(), 1);
    }

    #[test]
    fn test_base_child_parent() {
        let parent = new_base_node(None);
        let child = new_base_node(None);

        NodeInner::add_child_to_ref(&parent, child.clone());

        let retrieved_child = BaseNode::child(&parent, 0);
        assert_eq!(retrieved_child.borrow().id(), child.borrow().id());

        let retrieved_parent = BaseNode::parent(&child).expect("should have parent");
        assert_eq!(retrieved_parent.borrow().id(), parent.borrow().id());
    }
}
