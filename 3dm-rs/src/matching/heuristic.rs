//! Heuristic tree matching algorithm.
//!
//! This module implements the heuristic matching algorithm described in the
//! 3DM thesis. It finds correspondences between nodes in a base tree and a
//! branch tree using content hashing, fuzzy matching, and structural analysis.

use std::collections::HashSet;
use std::rc::Rc;

use crate::matching::constants::*;
use crate::matching::{CandidateEntry, DfsTreeIterator, Matching};
use crate::measure::Measure;
use crate::node::{MatchArea, MatchType, NodeInner, NodeRef, XmlContent};

/// Heuristic matching algorithm for building correspondences between trees.
///
/// This implementation follows the algorithm described in the 3DM thesis:
/// 1. Find candidate matches using exact content hash or fuzzy matching
/// 2. Score candidates by counting matching descendants (DFS match)
/// 3. Select best candidate, resolving ambiguities using sibling context
/// 4. Remove small copies below copy_threshold
/// 5. Match similar unmatched nodes to neighbors' siblings
/// 6. Set match types (FULL/CONTENT/CHILDREN) for copies
pub struct HeuristicMatching {
    /// Root of the base tree.
    base_root: Option<NodeRef>,
    /// Root of the branch tree.
    branch_root: Option<NodeRef>,
    /// Measure instance for distance calculations.
    measure: Measure,
    /// Whether this matching is for the left branch (vs right).
    is_left: bool,
    /// Threshold for considering a subtree to be copied.
    /// Subtrees smaller than this (in info bytes) are not considered copies.
    copy_threshold: i32,
}

impl Default for HeuristicMatching {
    fn default() -> Self {
        Self::new()
    }
}

impl HeuristicMatching {
    /// Creates a new HeuristicMatching instance with default copy threshold.
    pub fn new() -> Self {
        Self::with_copy_threshold(COPY_THRESHOLD)
    }

    /// Creates a new HeuristicMatching instance with custom copy threshold.
    pub fn with_copy_threshold(copy_threshold: i32) -> Self {
        HeuristicMatching {
            base_root: None,
            branch_root: None,
            measure: Measure::new(),
            is_left: true,
            copy_threshold,
        }
    }

    /// Creates a new HeuristicMatching and builds the matching.
    pub fn with_trees(base: &NodeRef, branch: &NodeRef) -> Self {
        let mut matching = Self::new();
        matching.build_matching(base, branch);
        matching
    }

    /// Sets whether this matching is for the left branch.
    pub fn set_is_left(&mut self, is_left: bool) {
        self.is_left = is_left;
    }

    /// Returns the copy threshold.
    pub fn copy_threshold(&self) -> i32 {
        self.copy_threshold
    }

    /// Main matching entry point for subtrees.
    fn match_subtrees(&mut self, base: &NodeRef, branch: &NodeRef) {
        // Find candidates for node branch in base
        let candidates = self.find_candidates(base, branch);

        // Find best matching trees by scoring with DFS
        let mut best_count = 0;
        let mut best_candidates: Vec<CandidateEntry> = Vec::new();

        for candidate in candidates {
            let this_count = self.dfs_match_count(&candidate.candidate, branch, 0);
            if this_count == best_count {
                best_candidates.push(candidate);
            } else if this_count > best_count {
                best_count = this_count;
                best_candidates.clear();
                best_candidates.push(candidate);
            }
        }

        // Add matchings and find nodes below matching subtree
        let best = self.get_best_candidate(branch, &mut best_candidates, best_count);
        let mut stop_nodes: Vec<NodeRef> = Vec::new();

        if let Some(best_entry) = best {
            let match_area = Rc::new(MatchArea::new(Rc::downgrade(branch)));
            self.dfs_match_add(&best_entry.candidate, branch, &mut stop_nodes, &match_area);
        } else {
            // Unmatched - all children become stop nodes
            let branch_borrowed = branch.borrow();
            for child in branch_borrowed.children() {
                stop_nodes.push(child.clone());
            }
        }

        // Recurse for stop nodes
        for stop_node in stop_nodes {
            self.match_subtrees(base, &stop_node);
        }
    }

    /// Find matching candidates for a node.
    fn find_candidates(&mut self, tree: &NodeRef, key: &NodeRef) -> Vec<CandidateEntry> {
        let mut candidates = Vec::new();
        self.find_exact_matches(tree, key, &mut candidates);
        if candidates.is_empty() {
            self.find_fuzzy_matches(tree, key, &mut candidates);
        }
        candidates
    }

    /// Find exact content matches.
    fn find_exact_matches(
        &self,
        tree: &NodeRef,
        key: &NodeRef,
        candidates: &mut Vec<CandidateEntry>,
    ) {
        let key_borrowed = key.borrow();
        let key_content = key_borrowed.content();

        for cand in DfsTreeIterator::new(tree.clone()) {
            let cand_borrowed = cand.borrow();
            if let (Some(key_c), Some(cand_c)) = (key_content, cand_borrowed.content()) {
                if cand_c.content_equals(key_c) {
                    drop(cand_borrowed);
                    candidates.push(CandidateEntry::new(cand, 0.0, -1.0));
                }
            }
        }
    }

    /// Find fuzzy matches for a node.
    fn find_fuzzy_matches(
        &mut self,
        tree: &NodeRef,
        key: &NodeRef,
        candidates: &mut Vec<CandidateEntry>,
    ) {
        let mut cset: Vec<CandidateEntry> = Vec::new();
        let mut cutoff = 2.0 * MAX_FUZZY_MATCH;

        for cand in DfsTreeIterator::new(tree.clone()) {
            let lrd_dist = self
                .get_distance_of_left(key, &cand)
                .min(self.get_distance_of_right(key, &cand))
                .min(self.measure.child_list_distance(key, &cand));

            let content_dist = self.measure.get_distance(Some(&cand), Some(key));
            let min_dist = lrd_dist.min(content_dist);

            if min_dist < 2.0 * MAX_FUZZY_MATCH {
                cset.push(CandidateEntry::new(cand, min_dist, lrd_dist));
                cutoff = cutoff.min(2.0 * min_dist);
            }
        }

        // Sort by distance
        cset.sort_by(|a, b| a.distance.partial_cmp(&b.distance).unwrap());

        // Add candidates within cutoff
        for entry in cset {
            if entry.distance > cutoff {
                break;
            }
            candidates.push(entry);
        }
    }

    /// Count matching nodes in subtrees (DFS match without adding matchings).
    fn dfs_match_count(&self, a: &NodeRef, b: &NodeRef, count: i32) -> i32 {
        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();

        let mut children_match = a_borrowed.child_count() == b_borrowed.child_count();

        if children_match {
            // Only match children if there are equally many
            for i in 0..a_borrowed.child_count() {
                let a_child = &a_borrowed.children()[i];
                let b_child = &b_borrowed.children()[i];

                let a_child_content = a_child.borrow().content().cloned();
                let b_child_content = b_child.borrow().content().cloned();

                if let (Some(ac), Some(bc)) = (a_child_content, b_child_content) {
                    if !ac.content_equals(&bc) {
                        children_match = false;
                        break;
                    }
                } else {
                    children_match = false;
                    break;
                }
            }
        }

        let mut result = count + 1;

        if children_match && a_borrowed.child_count() > 0 {
            let a_child = a_borrowed.children()[0].clone();
            let b_child = b_borrowed.children()[0].clone();
            drop(a_borrowed);
            drop(b_borrowed);
            result += self.dfs_match_count(&a_child, &b_child, 0);
            result += self.dfs_match_count_remaining(a, b, 1);
        }

        result
    }

    /// Helper to count remaining children after one iteration.
    fn dfs_match_count_remaining(&self, a: &NodeRef, b: &NodeRef, start: usize) -> i32 {
        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();

        if start < a_borrowed.child_count() {
            let a_child = a_borrowed.children()[start].clone();
            let b_child = b_borrowed.children()[start].clone();
            drop(a_borrowed);
            drop(b_borrowed);
            let result = self.dfs_match_count(&a_child, &b_child, 0);
            result + self.dfs_match_count_remaining(a, b, start + 1)
        } else {
            0
        }
    }

    /// DFS match with adding matchings and collecting stop nodes.
    fn dfs_match_add(
        &mut self,
        a: &NodeRef,
        b: &NodeRef,
        stop_nodes: &mut Vec<NodeRef>,
        match_area: &Rc<MatchArea>,
    ) {
        // Add matching
        self.add_matching(b, a);

        // Update match area info
        {
            let a_borrowed = a.borrow();
            if let Some(content) = a_borrowed.content() {
                match_area.add_info_bytes(content.info_size());
            }
        }

        // Set match area on branch node
        b.borrow_mut().set_match_area(Some(match_area.clone()));

        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();

        let mut children_match = a_borrowed.child_count() == b_borrowed.child_count();

        if children_match {
            for i in 0..a_borrowed.child_count() {
                let a_child = &a_borrowed.children()[i];
                let b_child = &b_borrowed.children()[i];

                let a_child_content = a_child.borrow().content().cloned();
                let b_child_content = b_child.borrow().content().cloned();

                if let (Some(ac), Some(bc)) = (a_child_content, b_child_content) {
                    if !ac.content_equals(&bc) {
                        children_match = false;
                        break;
                    }
                } else {
                    children_match = false;
                    break;
                }
            }
        }

        if !children_match {
            // Mark all children as stop nodes
            for child in b_borrowed.children() {
                stop_nodes.push(child.clone());
            }
        } else {
            // All children match - add edge info and recurse
            match_area.add_info_bytes(a_borrowed.child_count() as i32 * EDGE_BYTES);

            let children_a: Vec<NodeRef> = a_borrowed.children().to_vec();
            let children_b: Vec<NodeRef> = b_borrowed.children().to_vec();
            drop(a_borrowed);
            drop(b_borrowed);

            for (a_child, b_child) in children_a.iter().zip(children_b.iter()) {
                self.dfs_match_add(a_child, b_child, stop_nodes, match_area);
            }
        }
    }

    /// Select the best matching candidate from a set of candidates.
    fn get_best_candidate(
        &mut self,
        branch: &NodeRef,
        best_candidates: &mut [CandidateEntry],
        best_count: i32,
    ) -> Option<CandidateEntry> {
        if best_candidates.is_empty() {
            return None;
        }

        // Resolve ambiguities if multiple candidates
        if best_candidates.len() > 1 {
            // Check if left neighbor of candidate matches left of base
            let branch_borrowed = branch.borrow();
            if let Some(left_sibling) = NodeInner::left_sibling_of_ref(branch) {
                let left_base_match = {
                    let left_borrowed = left_sibling.borrow();
                    left_borrowed.get_base_match().and_then(|w| w.upgrade())
                };

                if let Some(left_base) = left_base_match {
                    for candidate in best_candidates.iter() {
                        let cand_left = NodeInner::left_sibling_of_ref(&candidate.candidate);
                        if let Some(cl) = cand_left {
                            if cl.borrow().id() == left_base.borrow().id() {
                                return Some(candidate.clone());
                            }
                        }
                    }
                }
            }
            drop(branch_borrowed);

            // Calculate missing left-right-down correlations
            for candidate in best_candidates.iter_mut() {
                if candidate.left_right_down < 0.0 {
                    let child_dist = self
                        .measure
                        .child_list_distance(&candidate.candidate, branch);
                    let left_dist = self.get_distance_of_left(&candidate.candidate, branch);
                    let right_dist = self.get_distance_of_right(&candidate.candidate, branch);
                    candidate.left_right_down = child_dist.min(left_dist).min(right_dist);
                }
            }

            // Sort by left-right-down distance
            best_candidates
                .sort_by(|a, b| a.left_right_down.partial_cmp(&b.left_right_down).unwrap());
        }

        let best = best_candidates.first().cloned();

        // Reject if single node match with poor context
        if let Some(ref b) = best {
            if best_count == 1 && b.left_right_down.min(b.distance) > 0.1 {
                return None;
            }
        }

        best
    }

    /// Match similar unmatched nodes to neighbors' siblings.
    fn match_similar_unmatched(&mut self, _base: &NodeRef, branch: &NodeRef) {
        // Traverse in preorder
        let children: Vec<NodeRef> = branch.borrow().children().to_vec();
        for child in &children {
            self.match_similar_unmatched(_base, child);
        }

        let base_match = {
            let branch_borrowed = branch.borrow();
            branch_borrowed.get_base_match().and_then(|w| w.upgrade())
        };

        if let Some(base_match) = base_match {
            let base_child_count = base_match.borrow().child_count();
            if base_child_count == 0 {
                return;
            }

            let branch_children: Vec<NodeRef> = branch.borrow().children().to_vec();
            let branch_child_count = branch_children.len();

            for (i, n) in branch_children.iter().enumerate() {
                // Skip if already matched
                if n.borrow().get_base_match().is_some() {
                    continue;
                }

                let last_base_child = base_child_count - 1;

                // Check endpoints
                if i == 0 {
                    let first_base_child = base_match.borrow().child(0).cloned();
                    if let Some(fbc) = first_base_child {
                        if !self.is_matched(&fbc) {
                            self.add_matching_if_same_type(n, &fbc);
                            continue;
                        }
                    }
                } else if i == branch_child_count - 1 {
                    let last_base = base_match.borrow().child(last_base_child).cloned();
                    if let Some(lbc) = last_base {
                        if !self.is_matched(&lbc) {
                            self.add_matching_if_same_type(n, &lbc);
                            continue;
                        }
                    }
                }

                // Check predecessor's right sibling
                if i > 0 {
                    let pred = &branch_children[i - 1];
                    let x = pred.borrow().get_base_match().and_then(|w| w.upgrade());
                    if let Some(x) = x {
                        if x.borrow().has_right_sibling() {
                            let right_sib = NodeInner::right_sibling_of_ref(&x);
                            if let Some(rs) = right_sib {
                                if !self.is_matched(&rs) {
                                    self.add_matching_if_same_type(n, &rs);
                                    continue;
                                }
                            }
                        }
                    }
                }

                // Check successor's left sibling
                if i < branch_child_count - 1 {
                    let succ = &branch_children[i + 1];
                    let x = succ.borrow().get_base_match().and_then(|w| w.upgrade());
                    if let Some(x) = x {
                        if x.borrow().has_left_sibling() {
                            let left_sib = NodeInner::left_sibling_of_ref(&x);
                            if let Some(ls) = left_sib {
                                if !self.is_matched(&ls) {
                                    self.add_matching_if_same_type(n, &ls);
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Remove copies smaller than COPY_THRESHOLD.
    fn remove_small_copies(&mut self, root: &NodeRef) {
        let base = {
            let root_borrowed = root.borrow();
            root_borrowed.get_base_match().and_then(|w| w.upgrade())
        };

        if let Some(base) = base {
            let match_count = self.get_match_count(&base);

            if match_count > 1 {
                let matches = self.get_matches(&base);
                let mut deletia: HashSet<u64> = HashSet::new();

                // Find copies that are too small
                for copy in &matches {
                    let info_bytes = {
                        let copy_borrowed = copy.borrow();
                        copy_borrowed
                            .match_area()
                            .map(|ma| ma.info_bytes())
                            .unwrap_or(0)
                    };

                    if info_bytes < self.copy_threshold {
                        deletia.insert(copy.borrow().id());
                    }
                }

                // If deleting all matches, keep the "original" instance
                if deletia.len() == matches.len() {
                    let mut max_copy_bytes = 0;
                    let mut orig_instance: Option<NodeRef> = None;

                    for copy in &matches {
                        let copy_bytes = self.calc_copy_context_bytes(copy);
                        if copy_bytes > max_copy_bytes {
                            max_copy_bytes = copy_bytes;
                            orig_instance = Some(copy.clone());
                        }
                    }

                    if let Some(orig) = orig_instance {
                        deletia.remove(&orig.borrow().id());
                        // Mark as original by adding info bytes
                        if let Some(ma) = orig.borrow().match_area() {
                            ma.add_info_bytes(self.copy_threshold + 1);
                        }
                    }
                }

                // Collect match areas to delete first
                let match_areas_to_delete: Vec<Rc<MatchArea>> = deletia
                    .iter()
                    .filter_map(|id| {
                        matches
                            .iter()
                            .find(|c| c.borrow().id() == *id)
                            .and_then(|copy| copy.borrow().match_area().cloned())
                    })
                    .collect();

                // Now delete them (no active borrows from matches)
                for ma in match_areas_to_delete {
                    self.del_match_area(&ma);
                }
            }
        }

        // Recurse for children
        let children: Vec<NodeRef> = root.borrow().children().to_vec();
        for child in children {
            self.remove_small_copies(&child);
        }
    }

    /// Calculate copy context bytes by scanning left and right siblings.
    fn calc_copy_context_bytes(&self, copy: &NodeRef) -> i32 {
        let match_area = copy.borrow().match_area().cloned();
        let mut copy_bytes = match_area.as_ref().map(|ma| ma.info_bytes()).unwrap_or(0);

        if copy_bytes >= self.copy_threshold {
            return copy_bytes;
        }

        let copy_root = match_area.as_ref().and_then(|ma| ma.root_strong());
        if copy_root.is_none() {
            return copy_bytes;
        }

        let copy_root = copy_root.unwrap();
        let copy_base = {
            let cr_borrowed = copy_root.borrow();
            cr_borrowed.get_base_match().and_then(|w| w.upgrade())
        };

        if copy_base.is_none() {
            return copy_bytes;
        }

        // Scan left siblings
        let mut curr_copy = copy_root.clone();
        let mut curr_base = copy_base.clone().unwrap();

        while copy_bytes < self.copy_threshold {
            let left_copy = NodeInner::left_sibling_of_ref(&curr_copy);
            let left_base = NodeInner::left_sibling_of_ref(&curr_base);

            match (left_copy, left_base) {
                (Some(lc), Some(lb)) => {
                    let lc_base = lc.borrow().get_base_match().and_then(|w| w.upgrade());
                    if lc_base.map(|b| b.borrow().id()) == Some(lb.borrow().id()) {
                        if let Some(ma) = lc.borrow().match_area() {
                            copy_bytes += ma.info_bytes();
                        }
                        curr_copy = lc;
                        curr_base = lb;
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }

        // Scan right siblings - get fresh copy_root reference
        let copy_root2 = match_area.as_ref().and_then(|ma| ma.root_strong());
        if let Some(cr2) = copy_root2 {
            curr_copy = cr2;
            curr_base = copy_base.unwrap();

            while copy_bytes < self.copy_threshold {
                let right_copy = NodeInner::right_sibling_of_ref(&curr_copy);
                let right_base = NodeInner::right_sibling_of_ref(&curr_base);

                match (right_copy, right_base) {
                    (Some(rc), Some(rb)) => {
                        let rc_base = rc.borrow().get_base_match().and_then(|w| w.upgrade());
                        if rc_base.map(|b| b.borrow().id()) == Some(rb.borrow().id()) {
                            if let Some(ma) = rc.borrow().match_area() {
                                copy_bytes += ma.info_bytes();
                            }
                            curr_copy = rc;
                            curr_base = rb;
                        } else {
                            break;
                        }
                    }
                    _ => break,
                }
            }
        }

        copy_bytes
    }

    /// Set match types for nodes with multiple matches.
    fn set_match_types(&mut self, base: &NodeRef) {
        // Postorder traversal
        let children: Vec<NodeRef> = base.borrow().children().to_vec();
        for child in children {
            self.set_match_types(&child);
        }

        let match_count = self.get_match_count(base);
        if match_count > 1 {
            // Has multiple matches - determine type of each copy
            let matches = self.get_matches(base);
            let mut min_dist = i32::MAX;
            let mut min_content_dist = f64::MAX;
            let mut master: Option<NodeRef> = None;

            for cand in &matches {
                let dist = if self.exact_child_list_match(base, cand) {
                    0
                } else {
                    self.measure
                        .matched_child_list_distance(base, cand, self.is_left)
                };

                if dist < min_dist {
                    min_dist = dist;
                    master = Some(cand.clone());
                } else if dist == min_dist {
                    // Calculate content distance for tie-breaking
                    let c_dist = self.measure.get_distance(Some(base), Some(cand));
                    if master.is_none() || c_dist < min_content_dist {
                        min_content_dist = c_dist;
                        master = Some(cand.clone());
                    }
                }
            }

            // Set match types for non-master copies
            let mut removed_matchings: Vec<NodeRef> = Vec::new();

            for cand in &matches {
                if master.as_ref().map(|m| m.borrow().id()) == Some(cand.borrow().id()) {
                    continue;
                }

                let struct_match = self.exact_child_list_match(base, cand);
                let cont_match = {
                    let cand_borrowed = cand.borrow();
                    let base_borrowed = base.borrow();
                    match (cand_borrowed.content(), base_borrowed.content()) {
                        (Some(cc), Some(bc)) => cc.content_equals(bc),
                        _ => false,
                    }
                };

                if !struct_match && !cont_match {
                    removed_matchings.push(cand.clone());
                } else {
                    let mut match_type = MatchType::NONE;
                    if cont_match {
                        match_type |= MatchType::CONTENT;
                    }
                    if struct_match {
                        match_type |= MatchType::CHILDREN;
                    }
                    cand.borrow_mut().set_match_type(match_type);
                }
            }

            // Delete removed matchings
            for cand in removed_matchings {
                if let Some(base_match) = cand.borrow().get_base_match().and_then(|w| w.upgrade()) {
                    self.del_matching(&cand, &base_match);
                }
            }
        }
    }

    /// Check if child lists are matched exactly.
    fn exact_child_list_match(&self, base: &NodeRef, branch: &NodeRef) -> bool {
        let base_borrowed = base.borrow();
        let branch_borrowed = branch.borrow();

        if base_borrowed.child_count() != branch_borrowed.child_count() {
            return false;
        }

        for i in 0..branch_borrowed.child_count() {
            let branch_child = &branch_borrowed.children()[i];
            let base_child = &base_borrowed.children()[i];

            let branch_child_base = branch_child
                .borrow()
                .get_base_match()
                .and_then(|w| w.upgrade());

            match branch_child_base {
                Some(bcb) if bcb.borrow().id() == base_child.borrow().id() => continue,
                _ => return false,
            }
        }

        true
    }

    /// Get content distance of left siblings.
    fn get_distance_of_left(&mut self, a: &NodeRef, b: &NodeRef) -> f64 {
        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();

        if a_borrowed.parent().upgrade().is_none() || b_borrowed.parent().upgrade().is_none() {
            return crate::measure::MAX_DIST;
        }

        let a_pos = a_borrowed.child_pos();
        let b_pos = b_borrowed.child_pos();

        drop(a_borrowed);
        drop(b_borrowed);

        if a_pos > 0 && b_pos > 0 {
            let a_left = NodeInner::left_sibling_of_ref(a);
            let b_left = NodeInner::left_sibling_of_ref(b);

            if let (Some(al), Some(bl)) = (a_left, b_left) {
                return self.measure.get_distance(Some(&al), Some(&bl));
            }
        }

        END_MATCH
    }

    /// Get content distance of right siblings.
    fn get_distance_of_right(&mut self, a: &NodeRef, b: &NodeRef) -> f64 {
        let a_borrowed = a.borrow();
        let b_borrowed = b.borrow();

        let a_parent = a_borrowed.parent().upgrade();
        let b_parent = b_borrowed.parent().upgrade();

        if a_parent.is_none() || b_parent.is_none() {
            return crate::measure::MAX_DIST;
        }

        let a_pos = a_borrowed.child_pos() as usize;
        let b_pos = b_borrowed.child_pos() as usize;
        let a_parent_count = a_parent.as_ref().unwrap().borrow().child_count();
        let b_parent_count = b_parent.as_ref().unwrap().borrow().child_count();

        drop(a_borrowed);
        drop(b_borrowed);

        if a_pos < a_parent_count - 1 && b_pos < b_parent_count - 1 {
            let a_right = NodeInner::right_sibling_of_ref(a);
            let b_right = NodeInner::right_sibling_of_ref(b);

            if let (Some(ar), Some(br)) = (a_right, b_right) {
                return self.measure.get_distance(Some(&ar), Some(&br));
            }
        }

        END_MATCH
    }

    /// Add matching if node types match (both text or both element).
    fn add_matching_if_same_type(&mut self, branch: &NodeRef, base: &NodeRef) {
        let branch_content = branch.borrow().content().cloned();
        let base_content = base.borrow().content().cloned();

        let same_type = matches!(
            (&branch_content, &base_content),
            (Some(XmlContent::Text(_)), Some(XmlContent::Text(_)))
                | (Some(XmlContent::Element(_)), Some(XmlContent::Element(_)))
        );

        if same_type {
            self.add_matching(branch, base);
        }
    }

    /// Add a matching between branch and base nodes.
    fn add_matching(&mut self, branch: &NodeRef, base: &NodeRef) {
        branch.borrow_mut().set_base_match(base);
        branch.borrow_mut().set_match_type(MatchType::FULL);

        // Add to base's left matches
        let base_borrowed = base.borrow();
        if let crate::node::NodeKind::Base { left, .. } = base_borrowed.kind() {
            left.borrow_mut().add_match(branch.clone());
        }
    }

    /// Delete a matching between branch and base nodes.
    fn del_matching(&mut self, branch: &NodeRef, base: &NodeRef) {
        branch.borrow_mut().del_base_match();

        // Remove from base's left matches
        let base_borrowed = base.borrow();
        if let crate::node::NodeKind::Base { left, .. } = base_borrowed.kind() {
            left.borrow_mut().del_match(branch);
        }
    }

    /// Delete a match area and all its matchings.
    fn del_match_area(&mut self, match_area: &Rc<MatchArea>) {
        if let Some(root) = match_area.root_strong() {
            self.del_match_area_recursive(&root, match_area);
        }
    }

    /// Recursive helper for deleting match area.
    fn del_match_area_recursive(&mut self, node: &NodeRef, match_area: &Rc<MatchArea>) {
        // Check if this node's match area matches what we're deleting
        // Use explicit scope to ensure borrow is dropped before mutable borrow
        let should_process = {
            let borrowed = node.borrow();
            borrowed
                .match_area()
                .map(|ma| Rc::ptr_eq(ma, match_area))
                .unwrap_or(false)
        };

        if should_process {
            node.borrow_mut().set_match_area(None);

            // Get base match in its own scope
            let base_match = {
                let borrowed = node.borrow();
                borrowed.get_base_match().and_then(|w| w.upgrade())
            };
            if let Some(base_match) = base_match {
                self.del_matching(node, &base_match);
            }

            // Get children in their own scope
            let children: Vec<NodeRef> = node.borrow().children().to_vec();
            for child in children {
                self.del_match_area_recursive(&child, match_area);
            }
        }
    }

    /// Check if a base node has any matches.
    fn is_matched(&self, base: &NodeRef) -> bool {
        self.get_match_count(base) > 0
    }

    /// Get match count for a base node.
    fn get_match_count(&self, base: &NodeRef) -> usize {
        let base_borrowed = base.borrow();
        if let crate::node::NodeKind::Base { left, .. } = base_borrowed.kind() {
            left.borrow().match_count()
        } else {
            0
        }
    }

    /// Get matches for a base node.
    fn get_matches(&self, base: &NodeRef) -> Vec<NodeRef> {
        let base_borrowed = base.borrow();
        if let crate::node::NodeKind::Base { left, .. } = base_borrowed.kind() {
            left.borrow().matches().to_vec()
        } else {
            Vec::new()
        }
    }
}

impl Matching for HeuristicMatching {
    fn build_matching(&mut self, base: &NodeRef, branch: &NodeRef) {
        self.base_root = Some(base.clone());
        self.branch_root = Some(branch.clone());

        self.match_subtrees(base, branch);
        self.remove_small_copies(branch);
        self.match_similar_unmatched(base, branch);
        self.set_match_types(base);

        // Artificial roots always matched
        branch.borrow_mut().set_base_match(base);
        branch.borrow_mut().set_match_type(MatchType::FULL);
    }

    fn get_area_stop_nodes(&self, stop_nodes: &mut Vec<NodeRef>, node: &NodeRef) {
        let parent_area = node.borrow().match_area().cloned();

        if parent_area.is_none() {
            panic!("ASSERT FAILED: node has no match area");
        }

        let parent_area = parent_area.unwrap();
        let mut children_in_same_area = true;

        {
            let node_borrowed = node.borrow();
            for child in node_borrowed.children() {
                let child_area = child.borrow().match_area().cloned();
                if child_area.as_ref().map(|ca| Rc::ptr_eq(ca, &parent_area)) != Some(true) {
                    children_in_same_area = false;
                    break;
                }
            }

            // BUGFIX 020115
            if node_borrowed.child_count() == 0 {
                if let Some(base_match) = node_borrowed.get_base_match().and_then(|w| w.upgrade()) {
                    if base_match.borrow().child_count() != 0 {
                        children_in_same_area = false;
                    }
                }
            }
        }

        if !children_in_same_area {
            stop_nodes.push(node.clone());
        } else {
            let children: Vec<NodeRef> = node.borrow().children().to_vec();
            for child in children {
                self.get_area_stop_nodes(stop_nodes, &child);
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
    use crate::node::{new_base_node, new_branch_node, XmlText};
    use std::collections::HashMap;

    fn make_element(name: &str) -> XmlContent {
        XmlContent::Element(crate::node::XmlElement::new(
            name.to_string(),
            HashMap::new(),
        ))
    }

    fn make_text(text: &str) -> XmlContent {
        XmlContent::Text(XmlText::new(text))
    }

    #[test]
    fn test_simple_matching() {
        // Base: <root><a/></root>
        // Branch: <root><a/></root>
        let base_root = new_base_node(Some(make_element("$ROOT$")));
        let base_a = new_base_node(Some(make_element("root")));
        let base_b = new_base_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&base_root, base_a.clone());
        NodeInner::add_child_to_ref(&base_a, base_b.clone());

        let branch_root = new_branch_node(Some(make_element("$ROOT$")));
        let branch_a = new_branch_node(Some(make_element("root")));
        let branch_b = new_branch_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&branch_root, branch_a.clone());
        NodeInner::add_child_to_ref(&branch_a, branch_b.clone());

        let mut matching = HeuristicMatching::new();
        matching.build_matching(&base_root, &branch_root);

        // All nodes should be matched
        assert!(branch_root.borrow().get_base_match().is_some());
        assert!(branch_a.borrow().get_base_match().is_some());
        assert!(branch_b.borrow().get_base_match().is_some());
    }

    #[test]
    fn test_text_matching() {
        let base_root = new_base_node(Some(make_element("$ROOT$")));
        let base_text = new_base_node(Some(make_text("hello world")));
        NodeInner::add_child_to_ref(&base_root, base_text.clone());

        let branch_root = new_branch_node(Some(make_element("$ROOT$")));
        let branch_text = new_branch_node(Some(make_text("hello world")));
        NodeInner::add_child_to_ref(&branch_root, branch_text.clone());

        let mut matching = HeuristicMatching::new();
        matching.build_matching(&base_root, &branch_root);

        assert!(branch_text.borrow().get_base_match().is_some());
    }

    #[test]
    fn test_unmatched_node() {
        // Base: <root><a/></root>
        // Branch: <root><b/></root>  (b doesn't exist in base)
        let base_root = new_base_node(Some(make_element("$ROOT$")));
        let base_a = new_base_node(Some(make_element("root")));
        let base_b = new_base_node(Some(make_element("a")));
        NodeInner::add_child_to_ref(&base_root, base_a.clone());
        NodeInner::add_child_to_ref(&base_a, base_b);

        let branch_root = new_branch_node(Some(make_element("$ROOT$")));
        let branch_a = new_branch_node(Some(make_element("root")));
        let branch_b = new_branch_node(Some(make_element("different_tag")));
        NodeInner::add_child_to_ref(&branch_root, branch_a.clone());
        NodeInner::add_child_to_ref(&branch_a, branch_b.clone());

        let mut matching = HeuristicMatching::new();
        matching.build_matching(&base_root, &branch_root);

        // Root and 'a' should match, 'b' should not (different tag)
        assert!(branch_root.borrow().get_base_match().is_some());
        assert!(branch_a.borrow().get_base_match().is_some());
        // 'different_tag' won't find exact match, fuzzy might or might not match
    }

    #[test]
    fn test_dfs_iterator() {
        let root = new_base_node(Some(make_element("root")));
        let a = new_base_node(Some(make_element("a")));
        let b = new_base_node(Some(make_element("b")));
        NodeInner::add_child_to_ref(&root, a.clone());
        NodeInner::add_child_to_ref(&root, b.clone());

        let iter = DfsTreeIterator::new(root);
        let count = iter.count();
        assert_eq!(count, 3);
    }
}
