//! Container for matched nodes.
//!
//! A `MatchedNodes` container holds references to branch nodes that are
//! matched to a specific base node.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::{Rc, Weak};

use super::{NodeInner, NodeRef};
use crate::node::MatchType;

/// A weak reference to a node.
pub type WeakNodeRef = Weak<RefCell<NodeInner>>;

/// Container for a set of branch nodes matched to a base node.
///
/// In the Java implementation, this uses a `HashSet` with identity-based
/// equality. We achieve the same by using node IDs for hashing.
#[derive(Debug, Clone)]
pub struct MatchedNodes {
    /// Weak reference to the owner base node.
    owner: WeakNodeRef,
    /// Set of matched branch node IDs.
    match_ids: HashSet<u64>,
    /// Strong references to matched branch nodes, keyed by node ID.
    /// We keep these to prevent nodes from being dropped.
    matches: Vec<NodeRef>,
}

impl MatchedNodes {
    /// Creates a new container for matched nodes.
    ///
    /// # Arguments
    /// * `owner` - Weak reference to the base node that owns this container.
    pub fn new(owner: WeakNodeRef) -> Self {
        MatchedNodes {
            owner,
            match_ids: HashSet::new(),
            matches: Vec::new(),
        }
    }

    /// Returns a weak reference to the owner base node.
    pub fn owner(&self) -> &WeakNodeRef {
        &self.owner
    }

    /// Adds a branch node to the match set.
    ///
    /// # Arguments
    /// * `node` - The branch node to add.
    pub fn add_match(&mut self, node: NodeRef) {
        let id = node.borrow().id();
        if self.match_ids.insert(id) {
            self.matches.push(node);
        }
    }

    /// Removes a branch node from the match set.
    ///
    /// # Arguments
    /// * `node` - The branch node to remove.
    pub fn del_match(&mut self, node: &NodeRef) {
        let id = node.borrow().id();
        if self.match_ids.remove(&id) {
            self.matches.retain(|n| n.borrow().id() != id);
        }
    }

    /// Clears all matches.
    pub fn clear_matches(&mut self) {
        self.match_ids.clear();
        self.matches.clear();
    }

    /// Returns the matched nodes.
    pub fn matches(&self) -> &[NodeRef] {
        &self.matches
    }

    /// Returns the number of matched nodes.
    pub fn match_count(&self) -> usize {
        self.matches.len()
    }

    /// Checks if a node is in the match set.
    pub fn contains(&self, node: &NodeRef) -> bool {
        let id = node.borrow().id();
        self.match_ids.contains(&id)
    }

    /// Gets the first node that is fully matched to the owner.
    ///
    /// A full match means both content and children match (MATCH_FULL).
    pub fn full_match(&self) -> Option<NodeRef> {
        for node in &self.matches {
            let borrowed = node.borrow();
            if let Some(match_type) = borrowed.match_type() {
                if match_type.contains(MatchType::FULL) {
                    return Some(Rc::clone(node));
                }
            }
        }
        None
    }
}

impl Default for MatchedNodes {
    fn default() -> Self {
        MatchedNodes {
            owner: Weak::new(),
            match_ids: HashSet::new(),
            matches: Vec::new(),
        }
    }
}
