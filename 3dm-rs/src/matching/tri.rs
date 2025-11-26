//! Three-way matching between a base and two branch trees.
//!
//! `TriMatching` coordinates matching between a base tree and two branch trees
//! (left and right). It uses a `Matching` implementation (typically `HeuristicMatching`)
//! to establish correspondences, then sets up the partner relationships between
//! nodes in the two branches via their common base matches.

use crate::node::base::BaseNode;
use crate::node::branch::BranchNode;
use crate::node::NodeRef;

use super::{HeuristicMatching, Matching};

/// Matching between a base and two branch trees.
///
/// This struct coordinates the matching process for 3-way merge:
/// 1. Matches the right branch against the base tree
/// 2. Swaps left/right matchings in base nodes (so right matchings become "right")
/// 3. Matches the left branch against the base tree
/// 4. Sets up partner relationships so each branch node knows its partners in the other branch
pub struct TriMatching {
    left_root: NodeRef,
    right_root: NodeRef,
    base_root: NodeRef,
}

impl TriMatching {
    /// Creates a new TriMatching using the default HeuristicMatching algorithm.
    pub fn new(left: NodeRef, base: NodeRef, right: NodeRef) -> Self {
        Self::with_matching::<HeuristicMatching, HeuristicMatching>(left, base, right)
    }

    /// Creates a new TriMatching with a custom copy threshold.
    ///
    /// The copy threshold determines the minimum size (in info bytes) for a
    /// subtree to be considered a copy. Smaller subtrees are treated as separate
    /// insertions. Use 0 to disable copy detection.
    pub fn with_copy_threshold(
        left: NodeRef,
        base: NodeRef,
        right: NodeRef,
        copy_threshold: i32,
    ) -> Self {
        // Match right branch first
        let mut right_matcher = HeuristicMatching::with_copy_threshold(copy_threshold);
        right_matcher.build_matching(&base, &right);

        // Swap left/right matchings in base tree
        Self::swap_left_right(&base);

        // Match left branch
        let mut left_matcher = HeuristicMatching::with_copy_threshold(copy_threshold);
        left_matcher.build_matching(&base, &left);

        // Set partner fields in both branches
        Self::set_partners(&left, false);
        Self::set_partners(&right, true);

        TriMatching {
            left_root: left,
            right_root: right,
            base_root: base,
        }
    }

    /// Creates a new TriMatching with custom matching algorithms.
    ///
    /// This allows using different matching strategies for left and right branches.
    /// For example, DiffMatching could be used for one branch if needed.
    pub fn with_matching<L: Matching + Default, R: Matching + Default>(
        left: NodeRef,
        base: NodeRef,
        right: NodeRef,
    ) -> Self {
        // Match right branch first
        let mut right_matcher = R::default();
        right_matcher.build_matching(&base, &right);

        // Swap left/right matchings in base tree
        // The matcher always populates "left" matches, so we need to swap
        // to put right matchings in the right field
        Self::swap_left_right(&base);

        // Match left branch
        let mut left_matcher = L::default();
        left_matcher.build_matching(&base, &left);

        // Set partner fields in both branches
        Self::set_partners(&left, false);
        Self::set_partners(&right, true);

        TriMatching {
            left_root: left,
            right_root: right,
            base_root: base,
        }
    }

    /// Recursively swaps left and right matching fields in base nodes.
    ///
    /// The HeuristicMatching always fills in the "left" matching field,
    /// so we call this after matching the right branch to move those
    /// matchings to the "right" field before matching the left branch.
    fn swap_left_right(base: &NodeRef) {
        BaseNode::swap_left_right_matchings(base);

        let children: Vec<NodeRef> = base.borrow().children().to_vec();
        for child in children {
            Self::swap_left_right(&child);
        }
    }

    /// Sets the partner fields of branch nodes.
    ///
    /// For each branch node with a base match, sets its partners to be
    /// the nodes from the other branch that match the same base node.
    ///
    /// # Arguments
    /// * `node` - The branch node to set partners for
    /// * `partner_in_left` - If true, partners are in the left tree; otherwise in the right tree
    fn set_partners(node: &NodeRef, partner_in_left: bool) {
        if let Some(base_match) = BranchNode::base_match(node) {
            // Get the partners from the other branch
            let partners = if partner_in_left {
                Some(BaseNode::left(&base_match))
            } else {
                Some(BaseNode::right(&base_match))
            };
            BranchNode::set_partners(node, partners);
        } else {
            BranchNode::set_partners(node, None);
        }

        // Recurse to children
        let children: Vec<NodeRef> = node.borrow().children().to_vec();
        for child in children {
            Self::set_partners(&child, partner_in_left);
        }
    }

    /// Returns a reference to the left branch root.
    pub fn left_root(&self) -> &NodeRef {
        &self.left_root
    }

    /// Returns a reference to the right branch root.
    pub fn right_root(&self) -> &NodeRef {
        &self.right_root
    }

    /// Returns a reference to the base tree root.
    pub fn base_root(&self) -> &NodeRef {
        &self.base_root
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_base_node, new_branch_node, NodeInner, XmlContent, XmlElement, XmlText};
    use std::collections::HashMap;

    fn make_element(name: &str) -> XmlContent {
        XmlContent::Element(XmlElement::new(name.to_string(), HashMap::new()))
    }

    fn make_text(text: &str) -> XmlContent {
        XmlContent::Text(XmlText::new(text))
    }

    #[test]
    fn test_tri_matching_simple() {
        // Create matching trees:
        // Base:  <root><a/></root>
        // Left:  <root><a/></root>
        // Right: <root><a/></root>

        let base_root = new_base_node(Some(make_element("root")));
        let base_a = new_base_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&base_root, base_a);

        let left_root = new_branch_node(Some(make_element("root")));
        let left_a = new_branch_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&left_root, left_a.clone());

        let right_root = new_branch_node(Some(make_element("root")));
        let right_a = new_branch_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&right_root, right_a.clone());

        let matching = TriMatching::new(left_root.clone(), base_root.clone(), right_root.clone());

        // Both branches should be matched
        assert!(BranchNode::has_base_match(&left_a));
        assert!(BranchNode::has_base_match(&right_a));

        // They should be partners (via base match)
        let left_partners = BranchNode::partners(&left_a);
        assert!(left_partners.is_some());
        let partners_borrowed = left_partners.unwrap();
        assert_eq!(partners_borrowed.borrow().match_count(), 1);

        // Verify tri-matching accessors
        assert_eq!(matching.left_root().borrow().id(), left_root.borrow().id());
        assert_eq!(
            matching.right_root().borrow().id(),
            right_root.borrow().id()
        );
        assert_eq!(matching.base_root().borrow().id(), base_root.borrow().id());
    }

    #[test]
    fn test_tri_matching_with_modifications() {
        // Base:  <root><a>text</a></root>
        // Left:  <root><a>modified</a></root>
        // Right: <root><a>text</a></root>

        let base_root = new_base_node(Some(make_element("root")));
        let base_a = new_base_node(Some(make_element("a")));
        let base_text = new_base_node(Some(make_text("text")));
        NodeInner::add_child_to_ref(&base_root, base_a.clone());
        NodeInner::add_child_to_ref(&base_a, base_text);

        let left_root = new_branch_node(Some(make_element("root")));
        let left_a = new_branch_node(Some(make_element("a")));
        let left_text = new_branch_node(Some(make_text("modified")));
        NodeInner::add_child_to_ref(&left_root, left_a.clone());
        NodeInner::add_child_to_ref(&left_a, left_text.clone());

        let right_root = new_branch_node(Some(make_element("root")));
        let right_a = new_branch_node(Some(make_element("a")));
        let right_text = new_branch_node(Some(make_text("text")));
        NodeInner::add_child_to_ref(&right_root, right_a.clone());
        NodeInner::add_child_to_ref(&right_a, right_text.clone());

        let _matching = TriMatching::new(left_root, base_root, right_root);

        // Element 'a' should be matched in both branches
        assert!(BranchNode::has_base_match(&left_a));
        assert!(BranchNode::has_base_match(&right_a));

        // Right text should match (identical)
        assert!(BranchNode::has_base_match(&right_text));

        // Left text might not match (different content) - depends on fuzzy matching
        // The actual result depends on the matching algorithm
    }

    #[test]
    fn test_tri_matching_unmatched_nodes() {
        // Base:  <root><a/></root>
        // Left:  <root><a/><b/></root>  (b is new)
        // Right: <root><a/></root>

        let base_root = new_base_node(Some(make_element("root")));
        let base_a = new_base_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&base_root, base_a);

        let left_root = new_branch_node(Some(make_element("root")));
        let left_a = new_branch_node(Some(make_element("a")));
        let left_b = new_branch_node(Some(make_element("b")));
        NodeInner::add_child_to_ref(&left_root, left_a.clone());
        NodeInner::add_child_to_ref(&left_root, left_b.clone());

        let right_root = new_branch_node(Some(make_element("root")));
        let right_a = new_branch_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&right_root, right_a.clone());

        let _matching = TriMatching::new(left_root, base_root, right_root);

        // 'a' should be matched in both
        assert!(BranchNode::has_base_match(&left_a));
        assert!(BranchNode::has_base_match(&right_a));

        // 'b' is new and should not have a base match
        assert!(!BranchNode::has_base_match(&left_b));

        // 'b' should have no partners
        assert!(BranchNode::partners(&left_b).is_none());
    }
}
