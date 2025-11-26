//! Merge pair structures for the 3-way merge algorithm.
//!
//! A MergePair represents a pair of nodes from the two branches that
//! should be merged together. A MergePairList is the result of merging
//! two MergeLists.

use crate::node::NodeRef;

/// A pair of nodes from the two branches to be merged.
///
/// Either node may be None if only one branch has content at this position.
#[derive(Debug, Clone)]
pub struct MergePair {
    /// The node from the first branch (left).
    pub first: Option<NodeRef>,
    /// The node from the second branch (right).
    pub second: Option<NodeRef>,
}

impl MergePair {
    /// Creates a new merge pair.
    pub fn new(first: Option<NodeRef>, second: Option<NodeRef>) -> Self {
        MergePair { first, second }
    }

    /// Returns the first node.
    pub fn first_node(&self) -> Option<&NodeRef> {
        self.first.as_ref()
    }

    /// Returns the second node.
    pub fn second_node(&self) -> Option<&NodeRef> {
        self.second.as_ref()
    }

    /// Returns true if both nodes are present.
    pub fn has_both(&self) -> bool {
        self.first.is_some() && self.second.is_some()
    }

    /// Returns true if at least one node is present.
    pub fn has_any(&self) -> bool {
        self.first.is_some() || self.second.is_some()
    }

    /// Returns the single node if only one is present.
    pub fn single_node(&self) -> Option<&NodeRef> {
        match (&self.first, &self.second) {
            (Some(n), None) | (None, Some(n)) => Some(n),
            _ => None,
        }
    }
}

/// A list of merge pairs representing the merged child list.
#[derive(Debug, Clone, Default)]
pub struct MergePairList {
    /// The pairs in the list.
    pairs: Vec<MergePair>,
}

impl MergePairList {
    /// Creates a new empty merge pair list.
    pub fn new() -> Self {
        MergePairList { pairs: Vec::new() }
    }

    /// Appends a pair to the list.
    pub fn append(&mut self, first: Option<NodeRef>, second: Option<NodeRef>) {
        self.pairs.push(MergePair::new(first, second));
    }

    /// Returns the number of pairs.
    pub fn pair_count(&self) -> usize {
        self.pairs.len()
    }

    /// Returns a pair by index.
    pub fn pair(&self, ix: usize) -> Option<&MergePair> {
        self.pairs.get(ix)
    }

    /// Returns all pairs.
    pub fn pairs(&self) -> &[MergePair] {
        &self.pairs
    }

    /// Returns a mutable reference to all pairs.
    pub fn pairs_mut(&mut self) -> &mut Vec<MergePair> {
        &mut self.pairs
    }

    /// Returns true if the list is empty.
    pub fn is_empty(&self) -> bool {
        self.pairs.is_empty()
    }
}

impl IntoIterator for MergePairList {
    type Item = MergePair;
    type IntoIter = std::vec::IntoIter<MergePair>;

    fn into_iter(self) -> Self::IntoIter {
        self.pairs.into_iter()
    }
}

impl<'a> IntoIterator for &'a MergePairList {
    type Item = &'a MergePair;
    type IntoIter = std::slice::Iter<'a, MergePair>;

    fn into_iter(self) -> Self::IntoIter {
        self.pairs.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_branch_node, XmlContent, XmlElement};

    fn make_element(name: &str) -> XmlContent {
        XmlContent::Element(XmlElement::new(
            name.to_string(),
            std::collections::HashMap::new(),
        ))
    }

    #[test]
    fn test_merge_pair_empty() {
        let pair = MergePair::new(None, None);
        assert!(!pair.has_both());
        assert!(!pair.has_any());
        assert!(pair.single_node().is_none());
    }

    #[test]
    fn test_merge_pair_first_only() {
        let node = new_branch_node(Some(make_element("a")));
        let pair = MergePair::new(Some(node.clone()), None);

        assert!(!pair.has_both());
        assert!(pair.has_any());
        assert!(pair.first_node().is_some());
        assert!(pair.second_node().is_none());
        assert!(pair.single_node().is_some());
    }

    #[test]
    fn test_merge_pair_second_only() {
        let node = new_branch_node(Some(make_element("b")));
        let pair = MergePair::new(None, Some(node.clone()));

        assert!(!pair.has_both());
        assert!(pair.has_any());
        assert!(pair.first_node().is_none());
        assert!(pair.second_node().is_some());
        assert!(pair.single_node().is_some());
    }

    #[test]
    fn test_merge_pair_both() {
        let a = new_branch_node(Some(make_element("a")));
        let b = new_branch_node(Some(make_element("b")));
        let pair = MergePair::new(Some(a), Some(b));

        assert!(pair.has_both());
        assert!(pair.has_any());
        assert!(pair.single_node().is_none());
    }

    #[test]
    fn test_merge_pair_list_empty() {
        let list = MergePairList::new();
        assert!(list.is_empty());
        assert_eq!(list.pair_count(), 0);
    }

    #[test]
    fn test_merge_pair_list_append() {
        let mut list = MergePairList::new();
        let a = new_branch_node(Some(make_element("a")));
        let b = new_branch_node(Some(make_element("b")));

        list.append(Some(a), None);
        list.append(None, Some(b));

        assert!(!list.is_empty());
        assert_eq!(list.pair_count(), 2);

        assert!(list.pair(0).unwrap().first_node().is_some());
        assert!(list.pair(1).unwrap().second_node().is_some());
    }

    #[test]
    fn test_merge_pair_list_iteration() {
        let mut list = MergePairList::new();
        list.append(None, None);
        list.append(None, None);
        list.append(None, None);

        let count = list.pairs().iter().count();
        assert_eq!(count, 3);
    }
}
