//! Node structures for XML tree representation.
//!
//! This module provides the core node types used to represent XML documents
//! as trees. The design mirrors the Java implementation with BaseNode and
//! BranchNode, unified into a single `NodeInner` with different `NodeKind`s.

pub mod base;
pub mod branch;
mod match_area;
mod matched_nodes;
mod xml_content;

pub use base::BaseNode;
pub use branch::BranchNode;
pub use match_area::{MatchArea, WeakNodeRef};
pub use matched_nodes::MatchedNodes;
pub use xml_content::{java_string_hash, XmlComment, XmlContent, XmlElement, XmlText};

use bitflags::bitflags;
use std::cell::RefCell;
use std::rc::{Rc, Weak};
use std::sync::atomic::{AtomicU64, Ordering};

/// Global counter for generating unique node IDs.
static NODE_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Generates a unique node ID.
fn next_node_id() -> u64 {
    NODE_ID_COUNTER.fetch_add(1, Ordering::Relaxed)
}

bitflags! {
    /// Match type flags indicating how a branch node matches its base node.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct MatchType: u8 {
        /// No match.
        const NONE = 0;
        /// Content (tag name and attributes, or text) matches.
        const CONTENT = 1;
        /// Children structure matches.
        const CHILDREN = 2;
        /// Both content and children match.
        const FULL = Self::CONTENT.bits() | Self::CHILDREN.bits();
    }
}

/// A reference-counted pointer to a node.
pub type NodeRef = Rc<RefCell<NodeInner>>;

/// Creates a new node reference.
pub fn new_node_ref(inner: NodeInner) -> NodeRef {
    Rc::new(RefCell::new(inner))
}

/// The inner data of a node in the parse tree.
///
/// Each node has:
/// - 0 or more children
/// - XML content (element or text)
/// - A parent (except for root)
/// - A position among siblings
/// - An optional match area tag
/// - Kind-specific data (Base or Branch)
#[derive(Debug)]
pub struct NodeInner {
    /// Unique identifier for this node.
    id: u64,
    /// Child nodes.
    children: Vec<NodeRef>,
    /// XML content of this node.
    content: Option<XmlContent>,
    /// Weak reference to parent node.
    parent: Weak<RefCell<NodeInner>>,
    /// Zero-based position among siblings (-1 for root).
    child_pos: i32,
    /// Match area tag for grouping matched subtrees.
    match_area: Option<Rc<MatchArea>>,
    /// Kind-specific data (Base or Branch).
    kind: NodeKind,
}

/// Kind-specific data for nodes.
#[derive(Debug)]
pub enum NodeKind {
    /// A base node matched to two branches.
    Base {
        /// Matches from the left branch.
        left: Rc<RefCell<MatchedNodes>>,
        /// Matches from the right branch.
        right: Rc<RefCell<MatchedNodes>>,
    },
    /// A branch node (left or right) matched to a base tree.
    Branch {
        /// The base node this branch node is matched to.
        base_match: Weak<RefCell<NodeInner>>,
        /// Partner nodes in the other branch tree.
        partners: Option<Rc<RefCell<MatchedNodes>>>,
        /// How this node matches its base node.
        match_type: MatchType,
        /// Whether this node is in the left tree.
        is_left_tree: Option<bool>,
    },
}

impl NodeInner {
    /// Creates a new base node with the given content.
    pub fn new_base(content: Option<XmlContent>) -> Self {
        let id = next_node_id();
        // Create a placeholder weak ref - will be set properly after node is wrapped in Rc
        let weak_self = Weak::new();
        let left = Rc::new(RefCell::new(MatchedNodes::new(weak_self.clone())));
        let right = Rc::new(RefCell::new(MatchedNodes::new(weak_self)));

        NodeInner {
            id,
            children: Vec::new(),
            content,
            parent: Weak::new(),
            child_pos: -1,
            match_area: None,
            kind: NodeKind::Base { left, right },
        }
    }

    /// Creates a new branch node with the given content.
    pub fn new_branch(content: Option<XmlContent>) -> Self {
        NodeInner {
            id: next_node_id(),
            children: Vec::new(),
            content,
            parent: Weak::new(),
            child_pos: -1,
            match_area: None,
            kind: NodeKind::Branch {
                base_match: Weak::new(),
                partners: None,
                match_type: MatchType::NONE,
                is_left_tree: None,
            },
        }
    }

    /// Returns the unique ID of this node.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Returns true if this is a base node.
    pub fn is_base(&self) -> bool {
        matches!(self.kind, NodeKind::Base { .. })
    }

    /// Returns true if this is a branch node.
    pub fn is_branch(&self) -> bool {
        matches!(self.kind, NodeKind::Branch { .. })
    }

    /// Returns the content of this node.
    pub fn content(&self) -> Option<&XmlContent> {
        self.content.as_ref()
    }

    /// Returns a mutable reference to the content.
    pub fn content_mut(&mut self) -> Option<&mut XmlContent> {
        self.content.as_mut()
    }

    /// Sets the content of this node.
    pub fn set_content(&mut self, content: Option<XmlContent>) {
        self.content = content;
    }

    /// Returns the number of children.
    pub fn child_count(&self) -> usize {
        self.children.len()
    }

    /// Returns a reference to the child at the given index.
    pub fn child(&self, index: usize) -> Option<&NodeRef> {
        self.children.get(index)
    }

    /// Returns the children as a slice.
    pub fn children(&self) -> &[NodeRef] {
        &self.children
    }

    /// Returns a weak reference to the parent.
    pub fn parent(&self) -> &Weak<RefCell<NodeInner>> {
        &self.parent
    }

    /// Returns the child position (0-based index among siblings, -1 for root).
    pub fn child_pos(&self) -> i32 {
        self.child_pos
    }

    /// Returns the match area, if set.
    pub fn match_area(&self) -> Option<&Rc<MatchArea>> {
        self.match_area.as_ref()
    }

    /// Sets the match area.
    pub fn set_match_area(&mut self, area: Option<Rc<MatchArea>>) {
        self.match_area = area;
    }

    /// Returns the node kind.
    pub fn kind(&self) -> &NodeKind {
        &self.kind
    }

    /// Returns a mutable reference to the node kind.
    pub fn kind_mut(&mut self) -> &mut NodeKind {
        &mut self.kind
    }

    /// Returns true if this node has a left sibling.
    pub fn has_left_sibling(&self) -> bool {
        self.child_pos > 0
    }

    /// Returns true if this node has a right sibling.
    pub fn has_right_sibling(&self) -> bool {
        if let Some(parent) = self.parent.upgrade() {
            let parent_borrowed = parent.borrow();
            self.child_pos >= 0 && (self.child_pos as usize) < parent_borrowed.children.len() - 1
        } else {
            false
        }
    }

    /// Returns the match type for branch nodes, None for base nodes.
    pub fn match_type(&self) -> Option<MatchType> {
        match &self.kind {
            NodeKind::Branch { match_type, .. } => Some(*match_type),
            NodeKind::Base { .. } => None,
        }
    }

    /// Returns the base match for branch nodes (a weak reference to the matched base node).
    /// Returns None for base nodes or if no match has been set.
    pub fn get_base_match(&self) -> Option<&Weak<RefCell<NodeInner>>> {
        match &self.kind {
            NodeKind::Branch { base_match, .. } => {
                // Return Some only if the weak ref is non-empty (can be upgraded)
                if base_match.strong_count() > 0 {
                    Some(base_match)
                } else {
                    None
                }
            }
            NodeKind::Base { .. } => None,
        }
    }

    /// Sets the base match for a branch node.
    /// Does nothing for base nodes.
    pub fn set_base_match(&mut self, base: &NodeRef) {
        if let NodeKind::Branch { base_match, .. } = &mut self.kind {
            *base_match = Rc::downgrade(base);
        }
    }

    /// Sets the match type for a branch node.
    /// Does nothing for base nodes.
    pub fn set_match_type(&mut self, mt: MatchType) {
        if let NodeKind::Branch { match_type, .. } = &mut self.kind {
            *match_type = mt;
        }
    }

    /// Clears the base match for a branch node.
    pub fn del_base_match(&mut self) {
        if let NodeKind::Branch { base_match, .. } = &mut self.kind {
            *base_match = Weak::new();
        }
    }
}

/// Helper functions that work with NodeRef.
impl NodeInner {
    /// Adds a child node. Must be called on the NodeRef wrapper.
    pub fn add_child_to_ref(parent_ref: &NodeRef, child_ref: NodeRef) {
        {
            let mut child = child_ref.borrow_mut();
            child.parent = Rc::downgrade(parent_ref);
            child.child_pos = parent_ref.borrow().children.len() as i32;
        }
        parent_ref.borrow_mut().children.push(child_ref);
    }

    /// Inserts a child at the given index.
    pub fn add_child_at_to_ref(parent_ref: &NodeRef, index: usize, child_ref: NodeRef) {
        {
            let mut child = child_ref.borrow_mut();
            child.parent = Rc::downgrade(parent_ref);
            child.child_pos = index as i32;
        }
        {
            let mut parent = parent_ref.borrow_mut();
            parent.children.insert(index, child_ref);
            // Update child positions for siblings after the insertion point
            for i in (index + 1)..parent.children.len() {
                parent.children[i].borrow_mut().child_pos = i as i32;
            }
        }
    }

    /// Replaces a child at the given index.
    pub fn replace_child_to_ref(parent_ref: &NodeRef, index: usize, child_ref: NodeRef) {
        let mut parent = parent_ref.borrow_mut();
        if index < parent.children.len() {
            parent.children[index] = child_ref;
        }
    }

    /// Removes the child at the given index.
    pub fn remove_child_to_ref(parent_ref: &NodeRef, index: usize) {
        let mut parent = parent_ref.borrow_mut();
        if index < parent.children.len() {
            parent.children.remove(index);
            // Update child positions for siblings after the removal point
            for i in index..parent.children.len() {
                parent.children[i].borrow_mut().child_pos = i as i32;
            }
        }
    }

    /// Removes all children.
    pub fn remove_children_to_ref(parent_ref: &NodeRef) {
        parent_ref.borrow_mut().children.clear();
    }

    /// Gets the left sibling of a node.
    pub fn left_sibling_of_ref(node_ref: &NodeRef) -> Option<NodeRef> {
        let node = node_ref.borrow();
        if node.child_pos <= 0 {
            return None;
        }
        if let Some(parent) = node.parent.upgrade() {
            let parent_borrowed = parent.borrow();
            let sibling_index = (node.child_pos - 1) as usize;
            parent_borrowed.children.get(sibling_index).cloned()
        } else {
            None
        }
    }

    /// Gets the right sibling of a node.
    pub fn right_sibling_of_ref(node_ref: &NodeRef) -> Option<NodeRef> {
        let node = node_ref.borrow();
        if node.child_pos < 0 {
            return None;
        }
        if let Some(parent) = node.parent.upgrade() {
            let parent_borrowed = parent.borrow();
            let sibling_index = (node.child_pos + 1) as usize;
            if sibling_index < parent_borrowed.children.len() {
                parent_borrowed.children.get(sibling_index).cloned()
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Initializes the owner weak refs for a base node's MatchedNodes.
    /// Must be called after the node is wrapped in Rc.
    pub fn init_base_node_owner(node_ref: &NodeRef) {
        let is_base = {
            let node = node_ref.borrow();
            matches!(node.kind, NodeKind::Base { .. })
        };

        if is_base {
            let weak_self = Rc::downgrade(node_ref);
            // We need to recreate the MatchedNodes with the proper owner
            let new_left = Rc::new(RefCell::new(MatchedNodes::new(weak_self.clone())));
            let new_right = Rc::new(RefCell::new(MatchedNodes::new(weak_self)));

            let mut node = node_ref.borrow_mut();
            if let NodeKind::Base { left, right } = &mut node.kind {
                *left = new_left;
                *right = new_right;
            }
        }
    }
}

/// Creates a new base node wrapped in NodeRef with properly initialized owner refs.
pub fn new_base_node(content: Option<XmlContent>) -> NodeRef {
    let node_ref = new_node_ref(NodeInner::new_base(content));
    NodeInner::init_base_node_owner(&node_ref);
    node_ref
}

/// Creates a new branch node wrapped in NodeRef.
pub fn new_branch_node(content: Option<XmlContent>) -> NodeRef {
    new_node_ref(NodeInner::new_branch(content))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_node_creation() {
        let base = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
            HashMap::new(),
        ))));
        assert!(base.borrow().is_base());
        assert!(!base.borrow().is_branch());

        let branch = new_branch_node(Some(XmlContent::Text(XmlText::new("hello"))));
        assert!(!branch.borrow().is_base());
        assert!(branch.borrow().is_branch());
    }

    #[test]
    fn test_add_child() {
        let parent = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "parent".to_string(),
            HashMap::new(),
        ))));
        let child1 = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "child1".to_string(),
            HashMap::new(),
        ))));
        let child2 = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "child2".to_string(),
            HashMap::new(),
        ))));

        NodeInner::add_child_to_ref(&parent, child1.clone());
        NodeInner::add_child_to_ref(&parent, child2.clone());

        assert_eq!(parent.borrow().child_count(), 2);
        assert_eq!(child1.borrow().child_pos(), 0);
        assert_eq!(child2.borrow().child_pos(), 1);
    }

    #[test]
    fn test_siblings() {
        let parent = new_base_node(None);
        let child1 = new_base_node(None);
        let child2 = new_base_node(None);
        let child3 = new_base_node(None);

        NodeInner::add_child_to_ref(&parent, child1.clone());
        NodeInner::add_child_to_ref(&parent, child2.clone());
        NodeInner::add_child_to_ref(&parent, child3.clone());

        // child1 has no left sibling, has right sibling
        assert!(!child1.borrow().has_left_sibling());
        assert!(child1.borrow().has_right_sibling());
        assert!(NodeInner::left_sibling_of_ref(&child1).is_none());
        assert!(NodeInner::right_sibling_of_ref(&child1).is_some());

        // child2 has both siblings
        assert!(child2.borrow().has_left_sibling());
        assert!(child2.borrow().has_right_sibling());
        let left = NodeInner::left_sibling_of_ref(&child2).unwrap();
        let right = NodeInner::right_sibling_of_ref(&child2).unwrap();
        assert_eq!(left.borrow().id(), child1.borrow().id());
        assert_eq!(right.borrow().id(), child3.borrow().id());

        // child3 has left sibling, no right sibling
        assert!(child3.borrow().has_left_sibling());
        assert!(!child3.borrow().has_right_sibling());
    }

    #[test]
    fn test_remove_child() {
        let parent = new_base_node(None);
        let child1 = new_base_node(None);
        let child2 = new_base_node(None);
        let child3 = new_base_node(None);

        NodeInner::add_child_to_ref(&parent, child1.clone());
        NodeInner::add_child_to_ref(&parent, child2.clone());
        NodeInner::add_child_to_ref(&parent, child3.clone());

        // Remove middle child
        NodeInner::remove_child_to_ref(&parent, 1);

        assert_eq!(parent.borrow().child_count(), 2);
        assert_eq!(child1.borrow().child_pos(), 0);
        assert_eq!(child3.borrow().child_pos(), 1);
    }

    #[test]
    fn test_insert_child() {
        let parent = new_base_node(None);
        let child1 = new_base_node(None);
        let child2 = new_base_node(None);
        let child3 = new_base_node(None);

        NodeInner::add_child_to_ref(&parent, child1.clone());
        NodeInner::add_child_to_ref(&parent, child3.clone());

        // Insert child2 in the middle
        NodeInner::add_child_at_to_ref(&parent, 1, child2.clone());

        assert_eq!(parent.borrow().child_count(), 3);
        assert_eq!(child1.borrow().child_pos(), 0);
        assert_eq!(child2.borrow().child_pos(), 1);
        assert_eq!(child3.borrow().child_pos(), 2);
    }

    #[test]
    fn test_match_type_flags() {
        assert_eq!(MatchType::FULL, MatchType::CONTENT | MatchType::CHILDREN);
        assert!(MatchType::FULL.contains(MatchType::CONTENT));
        assert!(MatchType::FULL.contains(MatchType::CHILDREN));
        assert!(!MatchType::CONTENT.contains(MatchType::CHILDREN));
    }

    #[test]
    fn test_unique_node_ids() {
        let node1 = new_base_node(None);
        let node2 = new_base_node(None);
        let node3 = new_branch_node(None);

        assert_ne!(node1.borrow().id(), node2.borrow().id());
        assert_ne!(node2.borrow().id(), node3.borrow().id());
        assert_ne!(node1.borrow().id(), node3.borrow().id());
    }
}
