//! BFS index for node enumeration.
//!
//! Assigns sequential IDs to nodes using breadth-first search traversal.
//! Adjacent nodes in the tree get consecutive IDs, enabling run-length encoding
//! in the diff output.

use std::collections::{HashMap, VecDeque};

use crate::node::NodeRef;

/// Index that maps nodes to sequential IDs using BFS order.
///
/// This allows the diff algorithm to use run-length encoding for
/// consecutive copies, as adjacent siblings will have sequential IDs.
#[derive(Debug)]
pub struct BfsIndex {
    /// Maps node IDs to their BFS index.
    node_to_id: HashMap<u64, u64>,
    /// Maps BFS index back to node.
    id_to_node: HashMap<u64, NodeRef>,
    /// The root node's ID.
    root_id: u64,
}

impl BfsIndex {
    /// Creates a new BFS index for the given tree.
    pub fn new(root: &NodeRef) -> Self {
        let mut node_to_id = HashMap::new();
        let mut id_to_node = HashMap::new();
        let mut queue = VecDeque::new();
        let mut id: u64 = 0;

        queue.push_back(root.clone());

        while let Some(node) = queue.pop_front() {
            let node_id = node.borrow().id();
            node_to_id.insert(node_id, id);
            id_to_node.insert(id, node.clone());

            // Add children to queue
            let borrowed = node.borrow();
            for child in borrowed.children() {
                queue.push_back(child.clone());
            }

            id += 1;
        }

        let root_id = *node_to_id.get(&root.borrow().id()).unwrap_or(&0);

        BfsIndex {
            node_to_id,
            id_to_node,
            root_id,
        }
    }

    /// Gets the BFS index for a node.
    pub fn get_id(&self, node: &NodeRef) -> Option<u64> {
        let node_id = node.borrow().id();
        self.node_to_id.get(&node_id).copied()
    }

    /// Looks up a node by its BFS index.
    pub fn lookup(&self, id: u64) -> Option<NodeRef> {
        self.id_to_node.get(&id).cloned()
    }

    /// Looks up a node by its string ID.
    pub fn lookup_str(&self, id: &str) -> Option<NodeRef> {
        id.parse::<u64>().ok().and_then(|n| self.lookup(n))
    }

    /// Returns the root node's BFS ID.
    pub fn root_id(&self) -> u64 {
        self.root_id
    }

    /// Checks if two nodes are adjacent in BFS order.
    pub fn appends(&self, tail: &NodeRef, next: &NodeRef) -> bool {
        match (self.get_id(tail), self.get_id(next)) {
            (Some(tail_id), Some(next_id)) => next_id == tail_id + 1,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::{new_base_node, NodeInner, XmlContent, XmlElement, XmlText};
    use std::collections::HashMap;

    fn create_test_tree() -> NodeRef {
        // Create tree:
        //     root
        //    /    \
        //  child1  child2
        //   |
        // grandchild
        let root = new_base_node(Some(XmlContent::Element(XmlElement::new(
            "root".to_string(),
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
        let grandchild = new_base_node(Some(XmlContent::Text(XmlText::new("text"))));

        // Build tree
        NodeInner::add_child_to_ref(&child1, grandchild);
        NodeInner::add_child_to_ref(&root, child1);
        NodeInner::add_child_to_ref(&root, child2);

        root
    }

    #[test]
    fn test_bfs_index_creation() {
        let root = create_test_tree();
        let index = BfsIndex::new(&root);

        // BFS order: root(0), child1(1), child2(2), grandchild(3)
        assert_eq!(index.root_id(), 0);
        assert_eq!(index.get_id(&root), Some(0));
    }

    #[test]
    fn test_bfs_lookup() {
        let root = create_test_tree();
        let index = BfsIndex::new(&root);

        // Lookup root
        let found = index.lookup(0).unwrap();
        assert_eq!(found.borrow().id(), root.borrow().id());

        // Lookup by string
        let found_str = index.lookup_str("0").unwrap();
        assert_eq!(found_str.borrow().id(), root.borrow().id());
    }

    #[test]
    fn test_bfs_appends() {
        let root = create_test_tree();
        let index = BfsIndex::new(&root);

        let child1 = index.lookup(1).unwrap();
        let child2 = index.lookup(2).unwrap();

        // child1 (1) and child2 (2) are adjacent
        assert!(index.appends(&child1, &child2));

        // root (0) and child2 (2) are not adjacent
        assert!(!index.appends(&root, &child2));
    }
}
