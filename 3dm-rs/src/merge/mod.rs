//! 3-way merge algorithm.
//!
//! This module implements the core 3-way merge algorithm that combines
//! two branch trees relative to a common base tree. The algorithm handles
//! insert, delete, update, move, and copy operations on subtrees.
//!
//! # Algorithm Overview
//!
//! The merge proceeds recursively through the matched trees:
//! 1. Create MergeLists for each branch's children
//! 2. Remove deleted/moved nodes and resolve conflicts
//! 3. Merge the lists into MergePairs
//! 4. For each pair, merge node content and recurse for children

mod conflict_log;
mod edit_log;
mod merge_list;
mod merge_pair;

pub use conflict_log::{ConflictLog, ConflictType};
pub use edit_log::{EditLog, EditType};
pub use merge_list::{MergeEntry, MergeList};
pub use merge_pair::{MergePair, MergePairList};

use std::io::Write;

use crate::matching::TriMatching;
use crate::node::base::BaseNode;
use crate::node::branch::BranchNode;
use crate::node::{MatchType, NodeRef, XmlContent, XmlElement};

/// Operation codes for merge list processing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Operation {
    /// No operation - node unchanged.
    Nop,
    /// Move inside child list.
    MoveI,
    /// Move far (to different parent).
    MoveF,
    /// Node deleted.
    Delete,
}

/// The main merge struct that orchestrates the 3-way merge.
pub struct Merge {
    /// The tri-matching with base, left, and right trees.
    matching: TriMatching,
    /// Log of conflicts encountered during merge.
    pub conflict_log: ConflictLog,
    /// Log of edit operations performed.
    pub edit_log: EditLog,
    /// Current indentation level for formatted output.
    indent: usize,
}

impl Merge {
    /// Creates a new Merge from a TriMatching.
    pub fn new(matching: TriMatching) -> Self {
        Merge {
            matching,
            conflict_log: ConflictLog::new(),
            edit_log: EditLog::new(),
            indent: 0,
        }
    }

    /// Returns a reference to the tri-matching.
    pub fn matching(&self) -> &TriMatching {
        &self.matching
    }

    /// Runs the 3-way merge and writes the result.
    ///
    /// The output is written as XML to the provided writer.
    pub fn merge<W: Write>(&mut self, writer: &mut W) -> std::io::Result<()> {
        // Start document
        writeln!(writer, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>")?;

        // Run the tree merge
        self.tree_merge(
            Some(self.matching.left_root().clone()),
            Some(self.matching.right_root().clone()),
            writer,
        )?;

        Ok(())
    }

    /// Main recursive merge function.
    ///
    /// Merges the child lists of a and b, then recurses for each child.
    fn tree_merge<W: Write>(
        &mut self,
        a: Option<NodeRef>,
        b: Option<NodeRef>,
        writer: &mut W,
    ) -> std::io::Result<()> {
        // Create merge lists for each branch
        let mlist_a = a.as_ref().map(|node| self.make_merge_list(node));
        let mlist_b = b.as_ref().map(|node| self.make_merge_list(node));

        // Generate merge pair list
        let merged = match (&mlist_a, &mlist_b) {
            (Some(ma), Some(mb)) => self.make_merge_pair_list(ma.clone(), mb.clone()),
            (Some(ma), None) => self.merge_list_to_pair_list(ma, None),
            (None, Some(mb)) => self.merge_list_to_pair_list(mb, None),
            (None, None) => MergePairList::new(),
        };

        // Process each merge pair
        for pair in merged.pairs() {
            let merged_node = self.merge_node_content(pair);

            if let Some(content) = &merged_node {
                match content {
                    XmlContent::Text(text) => {
                        // Output text content (with indentation only if on new line)
                        let text_str: String = text.text().iter().collect();
                        write!(
                            writer,
                            "{}{}",
                            Self::indent_str_for(self.indent),
                            escape_xml_text(&text_str)
                        )?;
                    }
                    XmlContent::Comment(comment) => {
                        // Output comment
                        let comment_text: String = comment.text().iter().collect();
                        writeln!(
                            writer,
                            "{}<!-- {} -->",
                            Self::indent_str_for(self.indent),
                            comment_text
                        )?;
                    }
                    XmlContent::Element(elem) => {
                        // Skip synthetic root
                        if elem.qname() == "$ROOT$" {
                            let partners = self.get_recursion_partners(pair);
                            self.tree_merge(partners.first, partners.second, writer)?;
                        } else {
                            // Output element start tag
                            self.write_start_element(writer, elem, self.indent)?;

                            // Increment indent for children
                            self.indent += 1;

                            // Get recursion partners and recurse
                            let partners = self.get_recursion_partners(pair);
                            self.tree_merge(partners.first, partners.second, writer)?;

                            // Decrement indent
                            self.indent -= 1;

                            // Output end tag
                            writeln!(
                                writer,
                                "{}</{}>",
                                Self::indent_str_for(self.indent),
                                elem.qname()
                            )?;
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Creates a merge list from the children of a branch node.
    fn make_merge_list(&mut self, parent: &NodeRef) -> MergeList {
        MergeList::from_branch(parent, &mut self.edit_log)
    }

    /// Merges two merge lists into a merge pair list.
    fn make_merge_pair_list(&mut self, mlist_a: MergeList, mlist_b: MergeList) -> MergePairList {
        let mut mlist_a = mlist_a;
        let mut mlist_b = mlist_b;

        // Remove deleted or far-moved nodes
        self.remove_deleted_or_moved(&mut mlist_a, &mut mlist_b);

        // Checkpoint for potential rollback
        self.edit_log.checkpoint();

        // Lists should now have the same entries
        if mlist_a.entry_count() != mlist_b.entry_count() {
            // Fallback to simpler merge
            self.edit_log.rewind();
            let is_left = mlist_a
                .entry_parent()
                .map(|p| BranchNode::is_left_tree(&p))
                .unwrap_or(true);
            return if is_left {
                self.merge_list_to_pair_list(&mlist_a, Some(&mlist_b))
            } else {
                self.merge_list_to_pair_list(&mlist_b, Some(&mlist_a))
            };
        }

        let mut merged = MergePairList::new();
        let mut pos_a = 0usize;
        let mut pos_b = 0usize;

        loop {
            let ea = mlist_a.entry(pos_a);
            let eb = mlist_b.entry(pos_b);

            if ea.is_none() || eb.is_none() {
                break;
            }

            let ea = ea.unwrap();
            let eb = eb.unwrap();

            // Add hangons from ea
            for hangon in ea.hangons() {
                let partner = hangon.borrow().first_partner(MatchType::FULL);
                merged.append(Some(hangon.clone()), partner);
                self.log_hangon_struct_ops(hangon);
            }

            // Add hangons from eb (if not equal to ea's hangons)
            if !self.check_hangon_combine(ea, eb) {
                for hangon in eb.hangons() {
                    let partner = hangon.borrow().first_partner(MatchType::FULL);
                    merged.append(Some(hangon.clone()), partner);
                    self.log_hangon_struct_ops(hangon);
                }
            }

            // Determine next positions
            let next_a: Option<usize>;
            let next_b: Option<usize>;

            let ea_locked = ea.locked && mlist_a.entry(pos_a + 1).is_some_and(|e| e.locked);
            let eb_locked = eb.locked && mlist_b.entry(pos_b + 1).is_some_and(|e| e.locked);

            if !ea_locked && !eb_locked {
                // No locking, both advance
                next_a = Some(pos_a + 1);
                next_b = Some(pos_b + 1);
            } else if ea_locked && !eb_locked {
                next_a = Some(pos_a + 1);
                next_b = mlist_b.find_partner_index(mlist_a.entry(pos_a + 1));
            } else if !ea_locked && eb_locked {
                next_b = Some(pos_b + 1);
                next_a = mlist_a.find_partner_index(mlist_b.entry(pos_b + 1));
            } else {
                // Both locked - check for conflict
                let partner_b = mlist_b.find_partner_index(mlist_a.entry(pos_a + 1));
                if partner_b != Some(pos_b + 1) {
                    // Conflict - fallback
                    self.conflict_log.add_list_conflict(
                        ConflictType::Move,
                        "Conflicting moves inside child list",
                        ea.node().and_then(|n| BranchNode::base_match(&n)),
                        ea.node(),
                        eb.node(),
                    );
                    self.edit_log.rewind();
                    let is_left = mlist_a
                        .entry_parent()
                        .map(|p| BranchNode::is_left_tree(&p))
                        .unwrap_or(true);
                    return if is_left {
                        self.merge_list_to_pair_list(&mlist_a, Some(&mlist_b))
                    } else {
                        self.merge_list_to_pair_list(&mlist_b, Some(&mlist_a))
                    };
                }
                next_a = Some(pos_a + 1);
                next_b = partner_b;
            }

            pos_a = next_a.unwrap_or(pos_a + 1);
            pos_b = next_b.unwrap_or(pos_b + 1);

            // Check if done (at END marker)
            if mlist_a.is_end(pos_a) || mlist_b.is_end(pos_b) {
                break;
            }

            // Add the main entry pair
            let ea = mlist_a.entry(pos_a);
            let eb = mlist_b.entry(pos_b);
            if let (Some(ea), Some(eb)) = (ea, eb) {
                merged.append(ea.node(), eb.node());
                self.log_entry_struct_ops(ea, eb);
            }
        }

        self.edit_log.commit();
        merged
    }

    /// Converts a single merge list to a pair list.
    fn merge_list_to_pair_list(
        &mut self,
        mlist_a: &MergeList,
        mlist_b: Option<&MergeList>,
    ) -> MergePairList {
        let mut merged = MergePairList::new();

        for (i, entry) in mlist_a.entries().iter().enumerate() {
            // Skip START marker but process its hangons
            if i > 0 && !mlist_a.is_end(i) {
                let node = entry.node();
                let partner = node
                    .as_ref()
                    .and_then(|n| n.borrow().first_partner(MatchType::FULL));
                merged.append(node, partner);
                if let Some(n) = entry.node() {
                    self.log_hangon_struct_ops(&n);
                }
            }

            // Add hangons
            for hangon in entry.hangons() {
                let partner = hangon.borrow().first_partner(MatchType::FULL);
                merged.append(Some(hangon.clone()), partner);
                self.log_hangon_struct_ops(hangon);
            }

            // Add hangons from mlist_b if present
            if let Some(mb) = mlist_b {
                if let Some(partner_entry) = mb.find_partner(entry) {
                    if !self.check_hangon_combine(entry, partner_entry) {
                        for hangon in partner_entry.hangons() {
                            let partner = hangon.borrow().first_partner(MatchType::FULL);
                            merged.append(Some(hangon.clone()), partner);
                            self.log_hangon_struct_ops(hangon);
                        }
                    }
                }
            }
        }

        merged
    }

    /// Removes deleted or far-moved nodes from merge lists.
    fn remove_deleted_or_moved(&mut self, mlist_a: &mut MergeList, mlist_b: &mut MergeList) {
        let base_parent = mlist_a
            .entry_parent()
            .and_then(|p| BranchNode::base_match(&p));

        if base_parent.is_none() {
            return;
        }

        let base_parent = base_parent.unwrap();
        let child_count = base_parent.borrow().child_count();

        for i in 0..child_count {
            let bn = base_parent.borrow().child(i).cloned();
            if bn.is_none() {
                continue;
            }
            let bn = bn.unwrap();

            let op1 = self.get_operation(&bn, mlist_a);
            let op2 = self.get_operation(&bn, mlist_b);

            // Handle based on which operation is smaller
            // The table is symmetric in terms of which list we apply actions to
            if op1 <= op2 {
                self.handle_operation_pair(op1, op2, &bn, mlist_a, mlist_b);
            } else {
                self.handle_operation_pair(op2, op1, &bn, mlist_b, mlist_a);
            }
        }
    }

    /// Handles a pair of operations on a base node.
    fn handle_operation_pair(
        &mut self,
        op1: Operation,
        op2: Operation,
        bn: &NodeRef,
        ml1: &mut MergeList,
        _ml2: &mut MergeList,
    ) {
        use Operation::*;

        match (op1, op2) {
            (Nop, Nop) | (Nop, MoveI) | (MoveI, MoveI) | (Delete, Delete) => {
                // OK cases - no action needed
            }
            (Nop, MoveF) | (Nop, Delete) => {
                // Delete the node from ml1
                if let Some(ix) = ml1.match_in_list(bn) {
                    if op2 == Delete {
                        // Check for modifications in deleted subtree
                        if let Some(entry) = ml1.entry(ix) {
                            if let Some(node) = entry.node() {
                                if self.is_deletia_modified(&node, ml1) {
                                    self.conflict_log.add_list_warning(
                                        ConflictType::Delete,
                                        "Modifications in deleted subtree",
                                        Some(bn.clone()),
                                        entry.node(),
                                        None,
                                    );
                                }
                            }
                        }
                        self.edit_log.delete(Some(bn.clone()));
                    }

                    // Move hangons to predecessor
                    ml1.move_hangons_to_predecessor(ix);
                    ml1.remove_entry_at(ix);
                }
            }
            (MoveI, MoveF) => {
                // Conflict: node moved to different locations
                if let Some(ix) = ml1.match_in_list(bn) {
                    let node = ml1.entry(ix).and_then(|e| e.node());
                    let partner = node
                        .as_ref()
                        .and_then(|n| n.borrow().first_partner(MatchType::FULL));
                    self.conflict_log.add_list_conflict(
                        ConflictType::Move,
                        "Node moved to different locations",
                        Some(bn.clone()),
                        node,
                        partner,
                    );
                    ml1.remove_entry_at(ix);
                }
            }
            (MoveI, Delete) => {
                // Conflict: node moved and deleted
                if let Some(ix) = ml1.match_in_list(bn) {
                    let node = ml1.entry(ix).and_then(|e| e.node());
                    self.conflict_log.add_list_conflict(
                        ConflictType::Move,
                        "Node moved and deleted",
                        Some(bn.clone()),
                        node,
                        None,
                    );
                    self.edit_log.delete(Some(bn.clone()));
                    ml1.remove_entry_at(ix);
                }
            }
            (MoveF, MoveF) => {
                // Check for movef-movef conflict
                if self.is_movef_movef_conflict(bn) {
                    self.conflict_log.add_list_conflict(
                        ConflictType::Move,
                        "Node moved to different locations",
                        Some(bn.clone()),
                        BaseNode::left(bn).borrow().full_match(),
                        BaseNode::right(bn).borrow().full_match(),
                    );
                }
            }
            (MoveF, Delete) => {
                // Conflict: moved and deleted - keep the move
                self.conflict_log.add_list_conflict(
                    ConflictType::Move,
                    "Node moved and deleted",
                    Some(bn.clone()),
                    BaseNode::left(bn).borrow().full_match(),
                    BaseNode::right(bn).borrow().full_match(),
                );
            }
            _ => {}
        }
    }

    /// Gets the operation on a base node in a merge list.
    fn get_operation(&self, bn: &NodeRef, ml: &MergeList) -> Operation {
        if let Some(pos) = ml.match_in_list(bn) {
            if ml.entry(pos).is_some_and(|e| e.moved) {
                Operation::MoveI
            } else {
                Operation::Nop
            }
        } else {
            // Check if moved far or deleted
            let is_left = ml
                .entry_parent()
                .map(|p| BranchNode::is_left_tree(&p))
                .unwrap_or(true);

            let copies = if is_left {
                BaseNode::left(bn)
            } else {
                BaseNode::right(bn)
            };

            if copies.borrow().match_count() == 0 {
                Operation::Delete
            } else {
                Operation::MoveF
            }
        }
    }

    /// Checks if a deleted subtree has modifications.
    fn is_deletia_modified(&self, n: &NodeRef, ml: &MergeList) -> bool {
        let base_match = BranchNode::base_match(n);
        if base_match.is_none() {
            return true; // Inserted node
        }

        let base_match = base_match.unwrap();
        if self.get_operation(&base_match, ml) != Operation::Nop {
            return true; // Node was moved
        }

        if BranchNode::base_match_type(n) != MatchType::FULL {
            return true; // Structural or content modification
        }

        // Check if deleted in other branch
        if let Some(partners) = BranchNode::partners(n) {
            if partners.borrow().match_count() == 0 {
                if !self.matches(n, &base_match) {
                    return true; // Updated
                }
                // Check children recursively
                for i in 0..n.borrow().child_count() {
                    if let Some(child) = n.borrow().child(i).cloned() {
                        // Would need child's merge list - simplify for now
                        if BranchNode::base_match_type(&child) != MatchType::FULL {
                            return true;
                        }
                    }
                }
            }
        }

        false
    }

    /// Checks for movef-movef conflict.
    ///
    /// A MoveF-MoveF conflict occurs when both branches move the same base node
    /// to different parent locations. Returns true if the parents differ (conflict).
    fn is_movef_movef_conflict(&self, bn: &NodeRef) -> bool {
        // Get left/right branch copies of base node
        let left_node = BaseNode::left(bn).borrow().full_match();
        let right_node = BaseNode::right(bn).borrow().full_match();

        let (left_node, right_node) = match (left_node, right_node) {
            (Some(l), Some(r)) => (l, r),
            _ => return false,
        };

        // Get parents
        let left_parent = BranchNode::parent(&left_node);
        let right_parent = BranchNode::parent(&right_node);

        match (left_parent, right_parent) {
            (Some(lp), Some(rp)) => {
                let lp_base = BranchNode::base_match(&lp);
                let rp_base = BranchNode::base_match(&rp);
                match (lp_base, rp_base) {
                    (Some(lb), Some(rb)) => lb.borrow().id() != rb.borrow().id(),
                    _ => true, // Inserted parent = conflict
                }
            }
            (None, None) => false, // Both at root
            _ => true,             // One at root, one not
        }
    }

    /// Merges the content of nodes in a merge pair.
    fn merge_node_content(&mut self, pair: &MergePair) -> Option<XmlContent> {
        let n1 = pair.first.as_ref();
        let n2 = pair.second.as_ref();

        match (n1, n2) {
            (None, None) => None,
            (Some(n), None) | (None, Some(n)) => n.borrow().content().cloned(),
            (Some(n1), Some(n2)) => {
                let n1_content = n1.borrow().is_match(MatchType::CONTENT);
                let n2_content = n2.borrow().is_match(MatchType::CONTENT);

                if n1_content {
                    if !n2_content {
                        self.edit_log.update(Some(n2.clone()));
                        n2.borrow().content().cloned()
                    } else {
                        self.content_merge(n1, n2)
                    }
                } else if n2_content {
                    self.edit_log.update(Some(n1.clone()));
                    n1.borrow().content().cloned()
                } else {
                    // Neither matches content - forced merge
                    self.content_merge(n1, n2)
                }
            }
        }
    }

    /// Merges content of two nodes.
    fn content_merge(&mut self, a: &NodeRef, b: &NodeRef) -> Option<XmlContent> {
        let base_a = BranchNode::base_match(a);
        let base_b = BranchNode::base_match(b);

        let a_updated = base_a.as_ref().is_none_or(|ba| !self.matches(a, ba));
        let b_updated = base_b.as_ref().is_none_or(|bb| !self.matches(b, bb));

        if a_updated && b_updated {
            // Both updated - check if same update
            if self.matches(a, b) {
                self.conflict_log.add_node_warning(
                    ConflictType::Update,
                    "Node updated in both branches, but updates are equal",
                    base_a.clone(),
                    Some(a.clone()),
                    Some(b.clone()),
                );
                self.edit_log.update(Some(a.clone()));
                return a.borrow().content().cloned();
            }

            // Try element merge
            if let Some(merged) = self.merge_elements(base_a.as_ref(), a, b) {
                return Some(merged);
            }

            // Conflict - use first branch
            self.conflict_log.add_node_conflict(
                ConflictType::Update,
                "Node updated in both branches, using branch 1",
                base_a,
                Some(a.clone()),
                Some(b.clone()),
            );
            self.edit_log.update(Some(a.clone()));
            a.borrow().content().cloned()
        } else if b_updated {
            self.edit_log.update(Some(b.clone()));
            b.borrow().content().cloned()
        } else if a_updated {
            self.edit_log.update(Some(a.clone()));
            a.borrow().content().cloned()
        } else {
            a.borrow().content().cloned()
        }
    }

    /// Attempts to merge two element nodes.
    fn merge_elements(
        &self,
        base: Option<&NodeRef>,
        a: &NodeRef,
        b: &NodeRef,
    ) -> Option<XmlContent> {
        let base_content = base.and_then(|n| n.borrow().content().cloned());
        let a_content = a.borrow().content().cloned();
        let b_content = b.borrow().content().cloned();

        match (&base_content, &a_content, &b_content) {
            (
                Some(XmlContent::Element(base_elem)),
                Some(XmlContent::Element(a_elem)),
                Some(XmlContent::Element(b_elem)),
            ) => {
                // Determine tag name
                let tag_name = if base_elem.qname() == b_elem.qname() {
                    a_elem.qname().to_string()
                } else if base_elem.qname() == a_elem.qname() {
                    b_elem.qname().to_string()
                } else {
                    return None; // Both changed tag name
                };

                // Merge attributes
                self.merge_attributes(
                    base_elem.attributes(),
                    a_elem.attributes(),
                    b_elem.attributes(),
                )
                .map(|merged_attrs| XmlContent::Element(XmlElement::new(tag_name, merged_attrs)))
            }
            _ => None,
        }
    }

    /// Merges attributes from base, a, and b.
    fn merge_attributes(
        &self,
        base: &std::collections::HashMap<String, String>,
        a: &std::collections::HashMap<String, String>,
        b: &std::collections::HashMap<String, String>,
    ) -> Option<std::collections::HashMap<String, String>> {
        let mut merged = std::collections::HashMap::new();
        let mut deletia = std::collections::HashSet::new();

        // Check for deleted attributes with conflicts
        for (key, base_val) in base {
            let in_a = a.get(key);
            let in_b = b.get(key);

            match (in_a, in_b) {
                (None, Some(b_val)) if base_val != b_val => return None, // Deleted and changed
                (Some(a_val), None) if base_val != a_val => return None, // Deleted and changed
                (None, _) | (_, None) => {
                    deletia.insert(key.clone());
                }
                _ => {}
            }
        }

        // Build merged attributes from a
        for (key, a_val) in a {
            if deletia.contains(key) {
                continue;
            }

            if let Some(b_val) = b.get(key) {
                let base_val = base.get(key);
                if base_val == Some(b_val) {
                    // A possibly updated
                    merged.insert(key.clone(), a_val.clone());
                } else if base_val == Some(a_val) {
                    // B possibly updated
                    merged.insert(key.clone(), b_val.clone());
                } else if a_val != b_val {
                    // Both changed differently
                    return None;
                } else {
                    merged.insert(key.clone(), a_val.clone());
                }
            } else {
                // Insert from a
                merged.insert(key.clone(), a_val.clone());
            }
        }

        // Add inserts from b
        for (key, b_val) in b {
            if !deletia.contains(key) && !a.contains_key(key) {
                merged.insert(key.clone(), b_val.clone());
            }
        }

        Some(merged)
    }

    /// Gets partners for recursion.
    fn get_recursion_partners(&self, pair: &MergePair) -> RecursionPartners {
        let n1 = pair.first.as_ref();
        let n2 = pair.second.as_ref();

        match (n1, n2) {
            (None, _) | (_, None) => RecursionPartners {
                first: pair.first.clone(),
                second: pair.second.clone(),
            },
            (Some(n1), Some(n2)) => {
                let n1_children = n1.borrow().is_match(MatchType::CHILDREN);
                let n2_children = n2.borrow().is_match(MatchType::CHILDREN);

                if n1_children && n2_children {
                    RecursionPartners {
                        first: Some(n1.clone()),
                        second: Some(n2.clone()),
                    }
                } else if n1_children && n2.borrow().is_match(MatchType::CONTENT) {
                    RecursionPartners {
                        first: None,
                        second: Some(n2.clone()),
                    }
                } else if n1.borrow().is_match(MatchType::CONTENT) && n2_children {
                    RecursionPartners {
                        first: Some(n1.clone()),
                        second: None,
                    }
                } else {
                    RecursionPartners {
                        first: Some(n1.clone()),
                        second: Some(n2.clone()),
                    }
                }
            }
        }
    }

    /// Checks if two nodes have equal content.
    fn matches(&self, a: &NodeRef, b: &NodeRef) -> bool {
        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();
        let a_content = a_borrowed.content();
        let b_content = b_borrowed.content();

        match (a_content, b_content) {
            (Some(ac), Some(bc)) => ac.content_equals(bc),
            _ => false,
        }
    }

    /// Logs structural operations for a hangon node.
    fn log_hangon_struct_ops(&mut self, n: &NodeRef) {
        if !BranchNode::has_base_match(n) {
            self.edit_log.insert(Some(n.clone()));
        } else {
            let base = BranchNode::base_match(n).unwrap();
            let is_left = BranchNode::is_left_tree(n);

            let copies = if is_left {
                BaseNode::left(&base)
            } else {
                BaseNode::right(&base)
            };

            if copies.borrow().match_count() > 1 {
                self.edit_log.copy(Some(n.clone()));
            } else {
                self.edit_log.r#move(Some(n.clone()));
            }
        }
    }

    /// Logs structural operations for merge entries.
    fn log_entry_struct_ops(&mut self, e1: &MergeEntry, e2: &MergeEntry) {
        if e1.moved {
            if let Some(n) = e1.node() {
                self.edit_log.r#move(Some(n));
            }
        } else if e2.moved {
            if let Some(n) = e2.node() {
                self.edit_log.r#move(Some(n));
            }
        }
    }

    /// Checks if hangons from two entries are equal.
    /// Returns true only if hangons match exactly (same count and content).
    /// When false, the caller should add eb's hangons to the merge list.
    fn check_hangon_combine(&mut self, ea: &MergeEntry, eb: &MergeEntry) -> bool {
        // If ea has no hangons, return false so eb's hangons are added
        if ea.hangons().is_empty() {
            return false;
        }

        if ea.hangons().len() != eb.hangons().len() {
            if !ea.hangons().is_empty() && !eb.hangons().is_empty() {
                self.conflict_log.add_list_warning(
                    ConflictType::Insert,
                    "Insertions/copies in both branches",
                    ea.node().and_then(|n| BranchNode::base_match(&n)),
                    ea.node(),
                    eb.node(),
                );
            }
            return false;
        }

        // Check if hangons match exactly
        let mut equal = true;
        for (ha, hb) in ea.hangons().iter().zip(eb.hangons().iter()) {
            if !self.tree_matches(ha, hb) {
                equal = false;
                break;
            }
        }

        if equal {
            self.conflict_log.add_list_warning(
                ConflictType::Insert,
                "Equal insertions/copies in both branches",
                ea.node().and_then(|n| BranchNode::base_match(&n)),
                ea.node(),
                eb.node(),
            );
        } else if !ea.hangons().is_empty() {
            self.conflict_log.add_list_warning(
                ConflictType::Insert,
                "Insertions/copies in both branches, sequencing",
                ea.node().and_then(|n| BranchNode::base_match(&n)),
                ea.node(),
                eb.node(),
            );
        }

        equal
    }

    /// Checks if entire subtrees match exactly.
    fn tree_matches(&self, a: &NodeRef, b: &NodeRef) -> bool {
        if !self.matches(a, b) {
            return false;
        }

        let a_count = a.borrow().child_count();
        let b_count = b.borrow().child_count();

        if a_count != b_count {
            return false;
        }

        for i in 0..a_count {
            let a_child = a.borrow().child(i).cloned();
            let b_child = b.borrow().child(i).cloned();

            match (a_child, b_child) {
                (Some(ac), Some(bc)) => {
                    if !self.tree_matches(&ac, &bc) {
                        return false;
                    }
                }
                _ => return false,
            }
        }

        true
    }

    /// Writes an element start tag.
    fn write_start_element<W: Write>(
        &self,
        writer: &mut W,
        elem: &XmlElement,
        indent: usize,
    ) -> std::io::Result<()> {
        write!(writer, "{}<{}", Self::indent_str_for(indent), elem.qname())?;

        // Write attributes (sorted for deterministic output)
        let mut attrs: Vec<(&String, &String)> = elem.attributes().iter().collect();
        attrs.sort_by(|a, b| a.0.cmp(b.0));

        for (name, value) in attrs {
            write!(writer, " {}=\"{}\"", name, escape_xml_attr(value))?;
        }

        writeln!(writer, ">")?;
        Ok(())
    }

    /// Returns the indentation string for a given level.
    fn indent_str_for(level: usize) -> String {
        "  ".repeat(level)
    }
}

/// Partners for recursion.
struct RecursionPartners {
    first: Option<NodeRef>,
    second: Option<NodeRef>,
}

/// Escapes special characters in XML text content.
fn escape_xml_text(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

/// Escapes special characters in XML attribute values.
fn escape_xml_attr(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&apos;")
}

impl crate::node::NodeInner {
    /// Returns the first partner that matches the given type.
    pub fn first_partner(&self, type_flags: MatchType) -> Option<NodeRef> {
        if let crate::node::NodeKind::Branch {
            match_type,
            partners,
            ..
        } = self.kind()
        {
            if !match_type.intersects(type_flags) {
                return None;
            }

            if let Some(partners) = partners {
                let borrowed = partners.borrow();
                for candidate in borrowed.matches() {
                    if BranchNode::base_match_type(candidate).intersects(type_flags) {
                        return Some(candidate.clone());
                    }
                }
            }
        }
        None
    }

    /// Returns true if the match type includes the given flags.
    pub fn is_match(&self, type_flags: MatchType) -> bool {
        if let crate::node::NodeKind::Branch { match_type, .. } = self.kind() {
            match_type.intersects(type_flags)
        } else {
            false
        }
    }
}
