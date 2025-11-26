//! Match area for tagging nodes in matched subtrees.
//!
//! A `MatchArea` is used to tag nodes that belong to the same matched subtree.
//! It contains a reference to the root of the subtree and an accumulated
//! information size metric.

use std::cell::{Cell, RefCell};
use std::rc::Weak;

use super::NodeInner;

/// A weak reference to a node, used to avoid reference cycles.
pub type WeakNodeRef = Weak<RefCell<NodeInner>>;

/// Tags nodes in the same matched subtree.
///
/// This is used during the matching phase to track which nodes belong
/// to a matched region and their combined information size.
#[derive(Debug)]
pub struct MatchArea {
    /// Accumulated information bytes in this subtree.
    /// Uses Cell for interior mutability since we need to update this
    /// through shared references (Rc<MatchArea>).
    info_bytes: Cell<i32>,
    /// Weak reference to the root node of this match area.
    /// The root is always a branch node.
    root: WeakNodeRef,
}

impl MatchArea {
    /// Creates a new match area with the given root node.
    pub fn new(root: WeakNodeRef) -> Self {
        MatchArea {
            info_bytes: Cell::new(0),
            root,
        }
    }

    /// Returns a reference to the root node weak reference.
    pub fn root(&self) -> &WeakNodeRef {
        &self.root
    }

    /// Returns the root as a strong reference if it still exists.
    pub fn root_strong(&self) -> Option<super::NodeRef> {
        self.root.upgrade()
    }

    /// Adds to the accumulated information bytes.
    pub fn add_info_bytes(&self, bytes: i32) {
        self.info_bytes.set(self.info_bytes.get() + bytes);
    }

    /// Returns the accumulated information bytes.
    pub fn info_bytes(&self) -> i32 {
        self.info_bytes.get()
    }
}
