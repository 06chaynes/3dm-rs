//! Diff-optimized tree matching.
//!
//! `DiffMatching` is a specialized matching algorithm for producing diffs.
//! Compared to the standard `HeuristicMatching`, it:
//! - Never uses fuzzy matching (only exact content matches)
//! - Prefers sequential matches (for efficient run-length encoding in diffs)
//! - Skips copy detection and similar-unmatched matching

use std::collections::HashMap;

use crate::node::{NodeInner, NodeRef};

use super::{CandidateEntry, DfsTreeIterator, Matching};

/// Tree matching algorithm optimized for diff generation.
///
/// This matching algorithm only uses exact content matches and prefers
/// sequential matches to enable efficient run-length encoding in the
/// generated diff output.
#[derive(Default)]
pub struct DiffMatching {
    base_root: Option<NodeRef>,
    branch_root: Option<NodeRef>,
    /// Hash index for fast candidate lookup.
    hash_index: HashMap<i32, Vec<NodeRef>>,
}

impl DiffMatching {
    /// Creates a new DiffMatching instance.
    pub fn new() -> Self {
        DiffMatching {
            base_root: None,
            branch_root: None,
            hash_index: HashMap::new(),
        }
    }

    /// Builds a hash index of all nodes in the base tree for fast lookup.
    fn build_hash_index(&mut self, base: &NodeRef) {
        self.hash_index.clear();

        for node in DfsTreeIterator::new(base.clone()) {
            if let Some(content) = node.borrow().content() {
                let hash = content.content_hash();
                self.hash_index.entry(hash).or_default().push(node.clone());
            }
        }
    }

    /// Matches subtrees starting from the given roots.
    fn match_subtrees(&mut self, base: &NodeRef, branch: &NodeRef) {
        self.build_hash_index(base);

        // Process all branch nodes
        let mut queue: Vec<NodeRef> = vec![branch.clone()];

        while let Some(current) = queue.pop() {
            // Find candidates for this node
            let candidates = self.find_candidates(&current);

            if candidates.is_empty() {
                // No match - all children become candidates
                let children: Vec<NodeRef> = current.borrow().children().to_vec();
                for child in children {
                    queue.push(child);
                }
            } else {
                // Get best candidate and add matching
                let best = self.get_best_candidate(&current, candidates);

                if let Some(best_entry) = best {
                    // Add matching and recurse for children
                    self.add_matching(&current, &best_entry.candidate);

                    // Get stop nodes (unmatched children)
                    let stop_nodes = self.get_stop_nodes(&best_entry.candidate, &current);
                    for stop_node in stop_nodes {
                        queue.push(stop_node);
                    }
                } else {
                    // No good candidate - all children become candidates
                    let children: Vec<NodeRef> = current.borrow().children().to_vec();
                    for child in children {
                        queue.push(child);
                    }
                }
            }
        }
    }

    /// Finds exact match candidates for a branch node.
    ///
    /// Unlike HeuristicMatching, DiffMatching only uses exact content matches.
    fn find_candidates(&self, branch: &NodeRef) -> Vec<CandidateEntry> {
        let mut candidates = Vec::new();

        let branch_borrowed = branch.borrow();
        if let Some(content) = branch_borrowed.content() {
            let hash = content.content_hash();

            if let Some(nodes) = self.hash_index.get(&hash) {
                for node in nodes {
                    // Verify exact content match
                    let node_borrowed = node.borrow();
                    if let Some(node_content) = node_borrowed.content() {
                        if content.content_equals(node_content) {
                            drop(node_borrowed);
                            candidates.push(CandidateEntry::new(node.clone(), 0.0, -1.0));
                        }
                    }
                }
            }
        }

        candidates
    }

    /// Selects the best candidate, preferring sequential matches.
    ///
    /// To enable efficient run-length encoding in diffs, we prefer candidates
    /// that are next to the previously matched node's base match.
    fn get_best_candidate(
        &self,
        branch: &NodeRef,
        candidates: Vec<CandidateEntry>,
    ) -> Option<CandidateEntry> {
        if candidates.is_empty() {
            return None;
        }

        // If multiple candidates, prefer one adjacent to left sibling's match
        if candidates.len() > 1 {
            if let Some(left_sibling) = NodeInner::left_sibling_of_ref(branch) {
                let left_base_match = left_sibling
                    .borrow()
                    .get_base_match()
                    .and_then(|w| w.upgrade());

                if let Some(left_base) = left_base_match {
                    // Find a candidate that is the right sibling of left's base match
                    for candidate in &candidates {
                        if let Some(cand_left) =
                            NodeInner::left_sibling_of_ref(&candidate.candidate)
                        {
                            if cand_left.borrow().id() == left_base.borrow().id() {
                                return Some(candidate.clone());
                            }
                        }
                    }
                }
            }
        }

        // Return first candidate
        candidates.into_iter().next()
    }

    /// Gets unmatched children after matching (stop nodes for further processing).
    fn get_stop_nodes(&self, base: &NodeRef, branch: &NodeRef) -> Vec<NodeRef> {
        let mut stop_nodes = Vec::new();

        let base_borrowed = base.borrow();
        let branch_borrowed = branch.borrow();

        let base_child_count = base_borrowed.child_count();
        let branch_child_count = branch_borrowed.child_count();

        // If same number of children, try to match them in order
        // Collect children first to avoid borrow issues
        let base_children: Vec<NodeRef> = base_borrowed.children().to_vec();
        let branch_children: Vec<NodeRef> = branch_borrowed.children().to_vec();
        drop(base_borrowed);
        drop(branch_borrowed);

        if base_child_count == branch_child_count {
            for i in 0..branch_child_count {
                let base_child = &base_children[i];
                let branch_child = &branch_children[i];

                // Check if contents match
                let base_content = base_child.borrow().content().cloned();
                let branch_content = branch_child.borrow().content().cloned();

                let matches = match (&base_content, &branch_content) {
                    (Some(bc), Some(rc)) => bc.content_equals(rc),
                    _ => false,
                };

                if matches {
                    // Add matching for children
                    self.add_matching(branch_child, base_child);

                    // Recursively get stop nodes from matched children
                    let child_stops = self.get_stop_nodes(base_child, branch_child);
                    stop_nodes.extend(child_stops);
                } else {
                    stop_nodes.push(branch_child.clone());
                }
            }
        } else {
            // Different child counts - all branch children are stop nodes
            for child in &branch_children {
                stop_nodes.push(child.clone());
            }
        }

        stop_nodes
    }

    /// Adds a matching between branch and base nodes.
    fn add_matching(&self, branch: &NodeRef, base: &NodeRef) {
        branch.borrow_mut().set_base_match(base);

        // Add to base's left matches
        let base_borrowed = base.borrow();
        if let crate::node::NodeKind::Base { left, .. } = base_borrowed.kind() {
            left.borrow_mut().add_match(branch.clone());
        }
    }

    /// Returns a reference to the branch root.
    pub fn branch_root_ref(&self) -> Option<&NodeRef> {
        self.branch_root.as_ref()
    }
}

impl Matching for DiffMatching {
    fn build_matching(&mut self, base: &NodeRef, branch: &NodeRef) {
        self.base_root = Some(base.clone());
        self.branch_root = Some(branch.clone());

        self.match_subtrees(base, branch);

        // Artificial roots always matched
        branch.borrow_mut().set_base_match(base);
    }

    fn get_area_stop_nodes(&self, stop_nodes: &mut Vec<NodeRef>, node: &NodeRef) {
        // For DiffMatching, stop nodes are simply unmatched children
        let children: Vec<NodeRef> = node.borrow().children().to_vec();
        for child in &children {
            if child.borrow().get_base_match().is_none() {
                stop_nodes.push(child.clone());
            } else {
                self.get_area_stop_nodes(stop_nodes, child);
                return;
            }
        }
    }

    fn base_root(&self) -> Option<&NodeRef> {
        self.base_root.as_ref()
    }

    fn branch_root(&self) -> Option<&NodeRef> {
        self.branch_root.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_base_node, new_branch_node, XmlContent, XmlElement, XmlText};

    fn make_element(name: &str) -> XmlContent {
        XmlContent::Element(XmlElement::new(
            name.to_string(),
            std::collections::HashMap::new(),
        ))
    }

    fn make_text(text: &str) -> XmlContent {
        XmlContent::Text(XmlText::new(text))
    }

    #[test]
    fn test_diff_matching_exact_only() {
        // Verify that DiffMatching only uses exact matches
        let base_root = new_base_node(Some(make_element("root")));
        let base_a = new_base_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&base_root, base_a.clone());

        let branch_root = new_branch_node(Some(make_element("root")));
        let branch_a = new_branch_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&branch_root, branch_a.clone());

        let mut matching = DiffMatching::new();
        matching.build_matching(&base_root, &branch_root);

        // Should match exactly
        assert!(branch_a.borrow().get_base_match().is_some());
    }

    #[test]
    fn test_diff_matching_no_fuzzy() {
        // Verify that similar but not identical content does NOT match
        let base_root = new_base_node(Some(make_element("root")));
        let base_text = new_base_node(Some(make_text("hello world")));
        NodeInner::add_child_to_ref(&base_root, base_text);

        let branch_root = new_branch_node(Some(make_element("root")));
        let branch_text = new_branch_node(Some(make_text("hello world!"))); // Different!
        NodeInner::add_child_to_ref(&branch_root, branch_text.clone());

        let mut matching = DiffMatching::new();
        matching.build_matching(&base_root, &branch_root);

        // Should NOT match (no fuzzy matching in DiffMatching)
        assert!(branch_text.borrow().get_base_match().is_none());
    }

    #[test]
    fn test_diff_matching_sequential_preference() {
        // Verify that DiffMatching prefers sequential matches
        // Base:  <root><a/><b/><a/></root>
        // Branch: <root><a/><b/><a/></root>
        // The second 'a' should match the second base 'a' (sequential), not the first

        let base_root = new_base_node(Some(make_element("root")));
        let base_a1 = new_base_node(Some(make_element("a")));
        let base_b = new_base_node(Some(make_element("b")));
        let base_a2 = new_base_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&base_root, base_a1.clone());
        NodeInner::add_child_to_ref(&base_root, base_b.clone());
        NodeInner::add_child_to_ref(&base_root, base_a2.clone());

        let branch_root = new_branch_node(Some(make_element("root")));
        let branch_a1 = new_branch_node(Some(make_element("a")));
        let branch_b = new_branch_node(Some(make_element("b")));
        let branch_a2 = new_branch_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&branch_root, branch_a1.clone());
        NodeInner::add_child_to_ref(&branch_root, branch_b.clone());
        NodeInner::add_child_to_ref(&branch_root, branch_a2.clone());

        let mut matching = DiffMatching::new();
        matching.build_matching(&base_root, &branch_root);

        // First 'a' should match first base 'a'
        let match1 = branch_a1
            .borrow()
            .get_base_match()
            .and_then(|w| w.upgrade());
        assert!(match1.is_some());
        assert_eq!(match1.unwrap().borrow().id(), base_a1.borrow().id());

        // Second 'a' should match second base 'a' (sequential preference)
        let match2 = branch_a2
            .borrow()
            .get_base_match()
            .and_then(|w| w.upgrade());
        assert!(match2.is_some());
        assert_eq!(match2.unwrap().borrow().id(), base_a2.borrow().id());
    }
}
