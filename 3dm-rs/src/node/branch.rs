//! Branch node helper functions.
//!
//! This module provides helper functions for working with branch nodes.
//! Branch nodes are nodes in a branch tree (left or right) that are matched
//! to nodes in the base tree.

use std::cell::RefCell;
use std::rc::{Rc, Weak};

use super::{MatchType, MatchedNodes, NodeInner, NodeKind, NodeRef};
use crate::error::{Error, Result};
use crate::node::base::BaseNode;

/// Helper functions for branch nodes.
pub struct BranchNode;

impl BranchNode {
    /// Sets the partners for a branch node.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn set_partners(node: &NodeRef, partners: Option<Rc<RefCell<MatchedNodes>>>) {
        let mut borrowed = node.borrow_mut();
        match &mut borrowed.kind {
            NodeKind::Branch {
                partners: p_field, ..
            } => {
                *p_field = partners;
            }
            NodeKind::Base { .. } => panic!("set_partners() called on base node"),
        }
    }

    /// Returns the partners for a branch node.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn partners(node: &NodeRef) -> Option<Rc<RefCell<MatchedNodes>>> {
        let borrowed = node.borrow();
        match &borrowed.kind {
            NodeKind::Branch { partners, .. } => partners.clone(),
            NodeKind::Base { .. } => panic!("partners() called on base node"),
        }
    }

    /// Sets the base match and match type for a branch node.
    ///
    /// # Arguments
    /// * `node` - The branch node
    /// * `base` - Weak reference to the base node
    /// * `match_type` - The match type (must be CONTENT, CHILDREN, or FULL)
    ///
    /// # Returns
    /// Error if match_type is invalid.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn set_base_match(
        node: &NodeRef,
        base: Weak<RefCell<NodeInner>>,
        match_type: MatchType,
    ) -> Result<()> {
        if match_type.bits() < MatchType::CONTENT.bits()
            || match_type.bits() > MatchType::FULL.bits()
        {
            return Err(Error::InvalidMatchType(match_type.bits()));
        }
        let mut borrowed = node.borrow_mut();
        match &mut borrowed.kind {
            NodeKind::Branch {
                base_match,
                match_type: mt,
                ..
            } => {
                *base_match = base;
                *mt = match_type;
                Ok(())
            }
            NodeKind::Base { .. } => panic!("set_base_match() called on base node"),
        }
    }

    /// Sets only the match type for a branch node.
    ///
    /// # Arguments
    /// * `node` - The branch node
    /// * `match_type` - The match type (must be CONTENT, CHILDREN, or FULL)
    ///
    /// # Returns
    /// Error if match_type is invalid.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn set_match_type(node: &NodeRef, match_type: MatchType) -> Result<()> {
        if match_type.bits() < MatchType::CONTENT.bits()
            || match_type.bits() > MatchType::FULL.bits()
        {
            return Err(Error::InvalidMatchType(match_type.bits()));
        }
        let mut borrowed = node.borrow_mut();
        match &mut borrowed.kind {
            NodeKind::Branch { match_type: mt, .. } => {
                *mt = match_type;
                Ok(())
            }
            NodeKind::Base { .. } => panic!("set_match_type() called on base node"),
        }
    }

    /// Clears the base match for a branch node.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn del_base_match(node: &NodeRef) {
        let mut borrowed = node.borrow_mut();
        match &mut borrowed.kind {
            NodeKind::Branch {
                base_match,
                match_type,
                ..
            } => {
                *base_match = Weak::new();
                *match_type = MatchType::NONE;
            }
            NodeKind::Base { .. } => panic!("del_base_match() called on base node"),
        }
    }

    /// Returns the match type for a branch node.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn base_match_type(node: &NodeRef) -> MatchType {
        let borrowed = node.borrow();
        match &borrowed.kind {
            NodeKind::Branch { match_type, .. } => *match_type,
            NodeKind::Base { .. } => panic!("base_match_type() called on base node"),
        }
    }

    /// Returns true if this branch node has a base match.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn has_base_match(node: &NodeRef) -> bool {
        let borrowed = node.borrow();
        match &borrowed.kind {
            NodeKind::Branch { base_match, .. } => base_match.upgrade().is_some(),
            NodeKind::Base { .. } => panic!("has_base_match() called on base node"),
        }
    }

    /// Returns the base match for a branch node.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn base_match(node: &NodeRef) -> Option<NodeRef> {
        let borrowed = node.borrow();
        match &borrowed.kind {
            NodeKind::Branch { base_match, .. } => base_match.upgrade(),
            NodeKind::Base { .. } => panic!("base_match() called on base node"),
        }
    }

    /// Returns true if this node is in the left tree.
    ///
    /// This is determined by checking if this node (or an ancestor) is in the
    /// left matches of its base match.
    ///
    /// # Panics
    /// Panics if the node is not a branch node, or if no matched ancestor is found.
    pub fn is_left_tree(node: &NodeRef) -> bool {
        // First check if we have a cached value
        {
            let borrowed = node.borrow();
            match &borrowed.kind {
                NodeKind::Branch { is_left_tree, .. } => {
                    if let Some(is_left) = is_left_tree {
                        return *is_left;
                    }
                }
                NodeKind::Base { .. } => panic!("is_left_tree() called on base node"),
            }
        }

        // Check if we have a base match
        if let Some(base) = BranchNode::base_match(node) {
            let left_matches = BaseNode::left(&base);
            return left_matches.borrow().contains(node);
        }

        // Recurse to parent
        let parent = {
            let borrowed = node.borrow();
            borrowed.parent().upgrade()
        };

        if let Some(p) = parent {
            BranchNode::is_left_tree(&p)
        } else {
            panic!("is_left_tree() called but no matched ancestor found")
        }
    }

    /// Sets the cached is_left_tree value.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn set_is_left_tree(node: &NodeRef, is_left: bool) {
        let mut borrowed = node.borrow_mut();
        match &mut borrowed.kind {
            NodeKind::Branch { is_left_tree, .. } => {
                *is_left_tree = Some(is_left);
            }
            NodeKind::Base { .. } => panic!("set_is_left_tree() called on base node"),
        }
    }

    /// Returns true if this node's match type includes the given flags.
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn is_match(node: &NodeRef, type_flags: MatchType) -> bool {
        let match_type = BranchNode::base_match_type(node);
        match_type.intersects(type_flags)
    }

    /// Finds the first partner node that matches the given type flags.
    ///
    /// For a node to be returned:
    /// 1. This node's match type must include the given flags
    /// 2. The partner's match type must include the given flags
    ///
    /// # Panics
    /// Panics if the node is not a branch node.
    pub fn first_partner(node: &NodeRef, type_flags: MatchType) -> Option<NodeRef> {
        let match_type = BranchNode::base_match_type(node);
        if !match_type.intersects(type_flags) {
            return None;
        }

        let partners = BranchNode::partners(node)?;
        let partners_borrowed = partners.borrow();

        for candidate in partners_borrowed.matches() {
            let candidate_type = BranchNode::base_match_type(candidate);
            if candidate_type.intersects(type_flags) {
                return Some(Rc::clone(candidate));
            }
        }

        None
    }

    /// Gets the child at the given index, asserting it's a branch node.
    ///
    /// # Panics
    /// Panics if the index is out of bounds or if the child is not a branch node.
    pub fn child(node: &NodeRef, index: usize) -> NodeRef {
        let borrowed = node.borrow();
        let child = borrowed
            .children()
            .get(index)
            .expect("child index out of bounds")
            .clone();
        assert!(child.borrow().is_branch(), "child is not a branch node");
        child
    }

    /// Gets the parent, asserting it's a branch node.
    ///
    /// Returns None if there is no parent.
    ///
    /// # Panics
    /// Panics if the parent exists but is not a branch node.
    pub fn parent(node: &NodeRef) -> Option<NodeRef> {
        let borrowed = node.borrow();
        borrowed.parent().upgrade().inspect(|p| {
            assert!(p.borrow().is_branch(), "parent is not a branch node");
        })
    }

    /// Checks if the given node is a branch node.
    pub fn is_branch(node: &NodeRef) -> bool {
        node.borrow().is_branch()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_base_node, new_branch_node, NodeInner};
    use std::rc::Rc;

    #[test]
    fn test_branch_base_match() {
        let base = new_base_node(None);
        let branch = new_branch_node(None);

        assert!(!BranchNode::has_base_match(&branch));

        BranchNode::set_base_match(&branch, Rc::downgrade(&base), MatchType::FULL).unwrap();

        assert!(BranchNode::has_base_match(&branch));
        assert_eq!(BranchNode::base_match_type(&branch), MatchType::FULL);

        let retrieved_base = BranchNode::base_match(&branch).expect("should have base match");
        assert_eq!(retrieved_base.borrow().id(), base.borrow().id());
    }

    #[test]
    fn test_invalid_match_type() {
        let base = new_base_node(None);
        let branch = new_branch_node(None);

        let result = BranchNode::set_base_match(&branch, Rc::downgrade(&base), MatchType::NONE);
        assert!(result.is_err());
    }

    #[test]
    fn test_del_base_match() {
        let base = new_base_node(None);
        let branch = new_branch_node(None);

        BranchNode::set_base_match(&branch, Rc::downgrade(&base), MatchType::FULL).unwrap();
        assert!(BranchNode::has_base_match(&branch));

        BranchNode::del_base_match(&branch);
        assert!(!BranchNode::has_base_match(&branch));
        assert_eq!(BranchNode::base_match_type(&branch), MatchType::NONE);
    }

    #[test]
    fn test_is_match() {
        let branch = new_branch_node(None);
        let base = new_base_node(None);

        // Set match type to CONTENT only
        BranchNode::set_base_match(&branch, Rc::downgrade(&base), MatchType::CONTENT).unwrap();

        // is_match uses bitwise AND (intersects), so:
        // - CONTENT & CONTENT = CONTENT (non-zero) -> true
        // - CONTENT & CHILDREN = 0 -> false
        // - CONTENT & FULL = CONTENT (non-zero) -> true (because FULL contains CONTENT)
        assert!(BranchNode::is_match(&branch, MatchType::CONTENT));
        assert!(!BranchNode::is_match(&branch, MatchType::CHILDREN));
        assert!(BranchNode::is_match(&branch, MatchType::FULL)); // CONTENT intersects FULL

        // Set match type to CHILDREN only
        BranchNode::set_match_type(&branch, MatchType::CHILDREN).unwrap();
        assert!(!BranchNode::is_match(&branch, MatchType::CONTENT));
        assert!(BranchNode::is_match(&branch, MatchType::CHILDREN));
        assert!(BranchNode::is_match(&branch, MatchType::FULL)); // CHILDREN intersects FULL

        // Set match type to FULL
        BranchNode::set_match_type(&branch, MatchType::FULL).unwrap();
        assert!(BranchNode::is_match(&branch, MatchType::CONTENT));
        assert!(BranchNode::is_match(&branch, MatchType::CHILDREN));
        assert!(BranchNode::is_match(&branch, MatchType::FULL));
    }

    #[test]
    fn test_partners() {
        let branch1 = new_branch_node(None);
        let branch2 = new_branch_node(None);
        let base = new_base_node(None);

        // Initially no partners
        assert!(BranchNode::partners(&branch1).is_none());

        // Set up partners via shared MatchedNodes
        let partners = Rc::new(RefCell::new(MatchedNodes::new(Rc::downgrade(&base))));
        partners.borrow_mut().add_match(branch2.clone());

        BranchNode::set_partners(&branch1, Some(partners));

        let retrieved_partners = BranchNode::partners(&branch1).expect("should have partners");
        assert_eq!(retrieved_partners.borrow().match_count(), 1);
    }

    #[test]
    fn test_branch_child_parent() {
        let parent = new_branch_node(None);
        let child = new_branch_node(None);

        NodeInner::add_child_to_ref(&parent, child.clone());

        let retrieved_child = BranchNode::child(&parent, 0);
        assert_eq!(retrieved_child.borrow().id(), child.borrow().id());

        let retrieved_parent = BranchNode::parent(&child).expect("should have parent");
        assert_eq!(retrieved_parent.borrow().id(), parent.borrow().id());
    }

    #[test]
    fn test_is_left_tree() {
        let base = new_base_node(None);
        let left_branch = new_branch_node(None);
        let right_branch = new_branch_node(None);

        // Set up matches
        BranchNode::set_base_match(&left_branch, Rc::downgrade(&base), MatchType::FULL).unwrap();
        BranchNode::set_base_match(&right_branch, Rc::downgrade(&base), MatchType::FULL).unwrap();

        // Add to left/right match sets
        BaseNode::left(&base)
            .borrow_mut()
            .add_match(left_branch.clone());
        BaseNode::right(&base)
            .borrow_mut()
            .add_match(right_branch.clone());

        assert!(BranchNode::is_left_tree(&left_branch));
        assert!(!BranchNode::is_left_tree(&right_branch));
    }

    #[test]
    fn test_first_partner() {
        let base = new_base_node(None);
        let branch1 = new_branch_node(None);
        let branch2 = new_branch_node(None);
        let branch3 = new_branch_node(None);

        // Set up branch1 with FULL match type
        BranchNode::set_base_match(&branch1, Rc::downgrade(&base), MatchType::FULL).unwrap();

        // Set up partners with different match types
        let partners = Rc::new(RefCell::new(MatchedNodes::new(Rc::downgrade(&base))));

        BranchNode::set_base_match(&branch2, Rc::downgrade(&base), MatchType::CONTENT).unwrap();
        BranchNode::set_base_match(&branch3, Rc::downgrade(&base), MatchType::CHILDREN).unwrap();

        partners.borrow_mut().add_match(branch2.clone());
        partners.borrow_mut().add_match(branch3.clone());

        BranchNode::set_partners(&branch1, Some(partners));

        // Find partner with CONTENT match
        let content_partner =
            BranchNode::first_partner(&branch1, MatchType::CONTENT).expect("should find partner");
        assert_eq!(content_partner.borrow().id(), branch2.borrow().id());

        // Find partner with CHILDREN match
        let children_partner =
            BranchNode::first_partner(&branch1, MatchType::CHILDREN).expect("should find partner");
        assert_eq!(children_partner.borrow().id(), branch3.borrow().id());
    }
}
