//! Merge list structures for the 3-way merge algorithm.
//!
//! A MergeList represents the children of a branch node organized for merging.
//! Each entry corresponds to a child, with additional "hangon" nodes that
//! represent inserts or copies that occur after that position.

use std::collections::HashMap;

use crate::node::{BranchNode, NodeRef};

use super::edit_log::EditLog;

/// A single entry in a merge list.
///
/// An entry contains a node and any "hangon" nodes that should be
/// placed after it in the merged output. Hangons are typically:
/// - Newly inserted nodes
/// - Nodes copied from elsewhere in the tree
/// - Far-moved nodes (moved from a different parent)
#[derive(Debug, Clone)]
pub struct MergeEntry {
    /// The main node for this entry, or None for START/END markers.
    node: Option<NodeRef>,
    /// Whether this is the START marker.
    pub is_start: bool,
    /// Whether this is the END marker.
    pub is_end: bool,
    /// Hangon nodes (inserts/copies after this position).
    hangons: Vec<NodeRef>,
    /// Whether this entry is locked (cannot be freely reordered).
    pub locked: bool,
    /// Whether this node was moved within the child list.
    pub moved: bool,
    /// Merge partner from the other branch (set during merge).
    merge_partner: Option<NodeRef>,
}

impl MergeEntry {
    /// Creates a new entry with the given node.
    pub fn new(node: Option<NodeRef>) -> Self {
        MergeEntry {
            node,
            is_start: false,
            is_end: false,
            hangons: Vec::new(),
            locked: false,
            moved: false,
            merge_partner: None,
        }
    }

    /// Creates the START marker entry.
    pub fn start() -> Self {
        MergeEntry {
            node: None,
            is_start: true,
            is_end: false,
            hangons: Vec::new(),
            locked: false,
            moved: false,
            merge_partner: None,
        }
    }

    /// Creates the END marker entry.
    pub fn end() -> Self {
        MergeEntry {
            node: None,
            is_start: false,
            is_end: true,
            hangons: Vec::new(),
            locked: false,
            moved: false,
            merge_partner: None,
        }
    }

    /// Returns the node for this entry.
    pub fn node(&self) -> Option<NodeRef> {
        self.node.clone()
    }

    /// Returns the hangon nodes.
    pub fn hangons(&self) -> &[NodeRef] {
        &self.hangons
    }

    /// Adds a hangon node.
    pub fn add_hangon(&mut self, node: NodeRef) {
        self.hangons.push(node);
    }

    /// Returns the number of hangon nodes.
    pub fn hangon_count(&self) -> usize {
        self.hangons.len()
    }

    /// Sets the merge partner.
    pub fn set_merge_partner(&mut self, partner: Option<NodeRef>) {
        self.merge_partner = partner;
    }

    /// Returns the merge partner.
    pub fn merge_partner(&self) -> Option<&NodeRef> {
        self.merge_partner.as_ref()
    }

    /// Returns the base match of this entry's node (if any).
    pub fn base_match(&self) -> Option<NodeRef> {
        self.node.as_ref().and_then(BranchNode::base_match)
    }
}

/// A list of merge entries for a branch node's children.
///
/// The merge list is used to track:
/// - Which children are present and in what order
/// - Which children have been moved within the list
/// - Which positions are "locked" (cannot be freely reordered)
/// - Hangon nodes at each position
#[derive(Debug, Clone)]
pub struct MergeList {
    /// The entries in the list.
    entries: Vec<MergeEntry>,
    /// Index from base match (node id) to entry position.
    index: HashMap<u64, usize>,
    /// The parent branch node.
    entry_parent: Option<NodeRef>,
    /// Current tail position (last valid entry).
    tail_pos: i32,
}

impl MergeList {
    /// Creates a new empty merge list.
    pub fn new(parent: Option<NodeRef>) -> Self {
        MergeList {
            entries: Vec::new(),
            index: HashMap::new(),
            entry_parent: parent,
            tail_pos: -1,
        }
    }

    /// Creates a merge list from a branch node's children.
    pub fn from_branch(parent: &NodeRef, edit_log: &mut EditLog) -> Self {
        let mut ml = MergeList::new(Some(parent.clone()));

        let base_match = BranchNode::base_match(parent);

        if base_match.is_none() {
            // Parent is unmatched - treat all children as inserts/copies
            ml.add_entry(MergeEntry::start());
            let child_count = parent.borrow().child_count();
            for i in 0..child_count {
                if let Some(child) = parent.borrow().child(i).cloned() {
                    ml.add_hangon(child);
                }
            }
            ml.lock_neighborhood(0, 1);
            ml.add_entry(MergeEntry::end());
            return ml;
        }

        let base_parent = base_match.unwrap();
        let mut base_matches: HashMap<u64, Option<usize>> = HashMap::new();
        let mut prev_child_pos: i32 = -1;

        ml.add_entry(MergeEntry::start());

        let child_count = parent.borrow().child_count();
        for i in 0..child_count {
            let current = match parent.borrow().child(i).cloned() {
                Some(c) => c,
                None => continue,
            };

            let current_base_match = BranchNode::base_match(&current);

            if let Some(base_node) = current_base_match {
                // Has a base match - check if it's from the expected parent
                let base_parent_match = {
                    let borrowed = base_node.borrow();
                    borrowed
                        .parent()
                        .upgrade()
                        .map(|p| p.borrow().id())
                        .unwrap_or(0)
                };
                let expected_parent_id = base_parent.borrow().id();

                if base_parent_match != expected_parent_id {
                    // Copied from elsewhere
                    ml.add_hangon(current);
                    ml.lock_neighborhood(0, 1);
                } else {
                    let base_id = base_node.borrow().id();

                    if base_matches.contains_key(&base_id) {
                        // N-th copy (n > 1)
                        ml.add_hangon(current);
                        if let Some(first_pos) = base_matches.get(&base_id).and_then(|p| *p) {
                            // Lock the first occurrence as well
                            ml.lock_neighborhood_at(first_pos, 1, 1);
                            // Put None to avoid locking more than once
                            base_matches.insert(base_id, None);
                        }
                        ml.lock_neighborhood(0, 1);
                    } else {
                        // Regular node from base
                        ml.add_node(current.clone());
                        base_matches.insert(base_id, Some(ml.tail_pos as usize));

                        let child_pos = base_node.borrow().child_pos();
                        let child_pos_i32 = if child_pos < 0 { -2 } else { child_pos };

                        if (prev_child_pos + 1) != child_pos_i32 {
                            // Out of sequence - check if actually moved
                            let mut moved = false;

                            if prev_child_pos != -2
                                && child_pos_i32 != -2
                                && prev_child_pos < child_pos_i32
                            {
                                // Check if nodes between prev and current are deleted
                                for j in 0..child_count {
                                    if let Some(sibling) = parent.borrow().child(j).cloned() {
                                        if let Some(sibling_base) = BranchNode::base_match(&sibling)
                                        {
                                            let base_pos = sibling_base.borrow().child_pos();
                                            if base_pos >= 0
                                                && base_pos > prev_child_pos
                                                && base_pos < child_pos_i32
                                            {
                                                moved = true;
                                                break;
                                            }
                                        }
                                    }
                                }
                            } else {
                                moved = true;
                            }

                            if moved {
                                ml.lock_neighborhood(1, 0);
                                ml.set_moved(true);
                            } else {
                                ml.set_moved(false);
                            }
                        }
                        prev_child_pos = child_pos_i32;
                    }
                }
            } else {
                // Insert node - no base match
                ml.add_hangon(current);
                ml.lock_neighborhood(0, 1);
            }
        }

        ml.add_entry(MergeEntry::end());

        // Check for end out-of-sequence
        let base_child_count = base_parent.borrow().child_count() as i32;
        if (prev_child_pos + 1) != base_child_count {
            ml.lock_neighborhood(1, 0);
        }

        // Suppress unused warning - edit_log is used in full implementation
        let _ = edit_log;

        ml
    }

    /// Adds an entry to the list.
    pub fn add_entry(&mut self, mut entry: MergeEntry) {
        self.tail_pos += 1;
        let pos = self.tail_pos as usize;

        // Ensure capacity
        while self.entries.len() <= pos {
            self.entries.push(MergeEntry::new(None));
        }

        // Preserve locked status from placeholder
        if let Some(existing) = self.entries.get(pos) {
            entry.locked = entry.locked || existing.locked;
        }

        // Index by base match
        if let Some(base) = entry.base_match() {
            let base_id = base.borrow().id();
            self.index.insert(base_id, pos);
        }

        self.entries[pos] = entry;
    }

    /// Adds a node as an entry.
    pub fn add_node(&mut self, node: NodeRef) {
        self.add_entry(MergeEntry::new(Some(node)));
    }

    /// Adds a hangon to the current entry.
    pub fn add_hangon(&mut self, node: NodeRef) {
        if self.tail_pos >= 0 {
            let pos = self.tail_pos as usize;
            if pos < self.entries.len() {
                self.entries[pos].add_hangon(node);
            }
        }
    }

    /// Sets the moved flag on the current entry.
    pub fn set_moved(&mut self, moved: bool) {
        if self.tail_pos >= 0 {
            let pos = self.tail_pos as usize;
            if pos < self.entries.len() {
                self.entries[pos].moved = moved;
            }
        }
    }

    /// Locks entries around the current position.
    pub fn lock_neighborhood(&mut self, left: usize, right: usize) {
        self.lock_neighborhood_at(self.tail_pos as usize, left, right);
    }

    /// Locks entries around the given position.
    pub fn lock_neighborhood_at(&mut self, pos: usize, left: usize, right: usize) {
        let end_pos = pos + right + 1;

        // Ensure capacity with locked placeholders
        while self.entries.len() < end_pos {
            self.entries.push(MergeEntry::new(None));
        }

        let start = pos.saturating_sub(left);
        let end = std::cmp::min(pos + right + 1, self.entries.len());

        for i in start..end {
            self.entries[i].locked = true;
        }
    }

    /// Returns the number of entries (including START and END).
    pub fn entry_count(&self) -> usize {
        (self.tail_pos + 1) as usize
    }

    /// Returns an entry by index.
    pub fn entry(&self, ix: usize) -> Option<&MergeEntry> {
        self.entries.get(ix)
    }

    /// Returns a mutable entry by index.
    pub fn entry_mut(&mut self, ix: usize) -> Option<&mut MergeEntry> {
        self.entries.get_mut(ix)
    }

    /// Returns all entries.
    pub fn entries(&self) -> &[MergeEntry] {
        &self.entries[..self.entry_count()]
    }

    /// Removes the entry at the given index.
    pub fn remove_entry_at(&mut self, ix: usize) {
        if ix < self.entries.len() {
            self.entries.remove(ix);
            self.tail_pos -= 1;

            // Rebuild index
            self.index.clear();
            for (i, entry) in self.entries.iter().enumerate() {
                if let Some(base) = entry.base_match() {
                    self.index.insert(base.borrow().id(), i);
                }
            }
        }
    }

    /// Moves hangons from entry at ix to its predecessor.
    pub fn move_hangons_to_predecessor(&mut self, ix: usize) {
        if ix > 0 && ix < self.entries.len() {
            let hangons: Vec<NodeRef> = self.entries[ix].hangons.drain(..).collect();
            for hangon in hangons {
                self.entries[ix - 1].add_hangon(hangon);
            }
        }
    }

    /// Finds the index of the partner entry (by base match).
    pub fn find_partner(&self, entry: &MergeEntry) -> Option<&MergeEntry> {
        let ix = self.find_partner_index(Some(entry))?;
        self.entries.get(ix)
    }

    /// Finds the index of the partner entry.
    pub fn find_partner_index(&self, entry: Option<&MergeEntry>) -> Option<usize> {
        let entry = entry?;

        if entry.is_start {
            return Some(0);
        }
        if entry.is_end {
            return Some(self.entry_count().saturating_sub(1));
        }

        let base = entry.base_match()?;
        let base_id = base.borrow().id();
        self.index.get(&base_id).copied()
    }

    /// Finds the index of a base node in the list.
    pub fn match_in_list(&self, base: &NodeRef) -> Option<usize> {
        let base_id = base.borrow().id();
        self.index.get(&base_id).copied()
    }

    /// Returns the entry parent.
    pub fn entry_parent(&self) -> Option<NodeRef> {
        self.entry_parent.clone()
    }

    /// Checks if the given index is the END marker.
    pub fn is_end(&self, ix: usize) -> bool {
        self.entries.get(ix).is_none_or(|e| e.is_end)
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
    fn test_merge_entry_basic() {
        let entry = MergeEntry::new(None);
        assert!(entry.node().is_none());
        assert!(!entry.is_start);
        assert!(!entry.is_end);
        assert!(!entry.locked);
        assert!(!entry.moved);
        assert_eq!(entry.hangon_count(), 0);
    }

    #[test]
    fn test_merge_entry_start_end() {
        let start = MergeEntry::start();
        assert!(start.is_start);
        assert!(!start.is_end);

        let end = MergeEntry::end();
        assert!(!end.is_start);
        assert!(end.is_end);
    }

    #[test]
    fn test_merge_entry_hangons() {
        let mut entry = MergeEntry::new(None);
        let node = new_branch_node(Some(make_element("child")));

        entry.add_hangon(node.clone());
        assert_eq!(entry.hangon_count(), 1);
        assert_eq!(entry.hangons()[0].borrow().id(), node.borrow().id());
    }

    #[test]
    fn test_merge_list_empty() {
        let ml = MergeList::new(None);
        assert_eq!(ml.entry_count(), 0);
        assert!(ml.entry_parent().is_none());
    }

    #[test]
    fn test_merge_list_add_entries() {
        let mut ml = MergeList::new(None);

        ml.add_entry(MergeEntry::start());
        assert_eq!(ml.entry_count(), 1);

        ml.add_node(new_branch_node(Some(make_element("a"))));
        assert_eq!(ml.entry_count(), 2);

        ml.add_entry(MergeEntry::end());
        assert_eq!(ml.entry_count(), 3);

        assert!(ml.entry(0).unwrap().is_start);
        assert!(ml.entry(2).unwrap().is_end);
    }

    #[test]
    fn test_merge_list_locking() {
        let mut ml = MergeList::new(None);

        ml.add_entry(MergeEntry::start());
        ml.add_node(new_branch_node(Some(make_element("a"))));
        ml.add_node(new_branch_node(Some(make_element("b"))));
        ml.add_entry(MergeEntry::end());

        ml.lock_neighborhood_at(1, 1, 1);

        assert!(ml.entry(0).unwrap().locked);
        assert!(ml.entry(1).unwrap().locked);
        assert!(ml.entry(2).unwrap().locked);
        assert!(!ml.entry(3).unwrap().locked);
    }

    #[test]
    fn test_merge_list_remove_entry() {
        let mut ml = MergeList::new(None);

        ml.add_entry(MergeEntry::start());
        ml.add_node(new_branch_node(Some(make_element("a"))));
        ml.add_node(new_branch_node(Some(make_element("b"))));
        ml.add_entry(MergeEntry::end());

        assert_eq!(ml.entry_count(), 4);

        ml.remove_entry_at(2);
        assert_eq!(ml.entry_count(), 3);
    }
}
