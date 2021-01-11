//! Node type for WordFilter's internal directional graph.
//!
//! The graph defined by these Nodes is basically a Trie with a few extra attributes. Edges between
//! nodes are defined by characters (UTF-8), and traversal through the graph is done through those
//! characters.

//! In addition to the standard parent-child path, aliases can also be represented as references to
//! other subgraphs. Those subgraphs may end in Return nodes, linking the path back to the
//! supergraph.
//!
//! Each node also has a NodeType, identifying what kind of Node it is.

use std::{collections::HashMap, pin::Pin};

#[derive(Debug, PartialEq)]
pub enum NodeType<'a> {
    Standard,
    Match(&'a str),
    Exception(&'a str),
    Return,
}

/// A Trie structure node.
///
/// It represents a directional graph with character edges. Each Node has defined children, as well
/// as possible alias subgraphs to be traveled on as well.
///
/// Each Node also has a node_type, defining what kind of node it is. These are useful if the user
/// wishes to know whether they are at a match, an exception, or perhaps a subgraph return.
pub struct Node<'a> {
    /// All children Nodes, keyed by character edges.
    pub children: HashMap<char, Pin<Box<Node<'a>>>>,

    /// Any alternative subgraphs that can be traveled from this node.
    ///
    /// These are pairs representing `(sub_graph_node, return_node)`.
    pub aliases: Vec<(&'a Node<'a>, &'a Node<'a>)>,

    /// The type of node.
    pub node_type: NodeType<'a>,
}

impl<'a> Node<'a> {
    /// Creates a new Standard node.
    ///
    /// All internal fields are initialized to be empty.
    pub fn new() -> Self {
        Self {
            children: HashMap::new(),
            aliases: Vec::new(),
            node_type: NodeType::Standard,
        }
    }

    /// Converts the Node to a raw pointer.
    ///
    /// The caller must ensure the returned pointer is never written to.
    pub fn as_ptr(&self) -> *const u8 {
        self as *const Node as *const u8
    }

    fn add_path(&mut self, word: &str, node_type: NodeType<'a>) {
        if word.is_empty() {
            if match self.node_type {
                NodeType::Standard => true,
                _ => false,
            } {
                self.node_type = node_type;
            }
            return;
        }

        let mut char_indices = word.char_indices();
        self.children
            .entry(char_indices.next().map(|(_index, c)| c).unwrap())
            .or_insert_with(|| Box::pin(Self::new()))
            .add_path(
                &word[char_indices
                    .next()
                    .map(|(index, _c)| index)
                    .unwrap_or_else(|| word.len())..],
                node_type,
            );
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as a Match.
    pub fn add_match(&mut self, word: &'a str) {
        self.add_path(word, NodeType::Match(word));
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as an Exception.
    pub fn add_exception(&mut self, word: &'a str) {
        self.add_path(word, NodeType::Exception(word));
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as a Return.
    pub fn add_return(&mut self, word: &str) {
        self.add_path(word, NodeType::Return);
    }

    fn find_alias_return_node(&self, value: &str) -> Option<&'a Node<'a>> {
        if value.is_empty() {
            // Unsafe is needed to return a reference while also releasing the borrow. If the Node
            // is ever deleted, this becomes unbounded. However, this should not happen, as Nodes
            // are only ever added to the WordFilter graph.
            unsafe {
                return Some((self.as_ptr() as *const Node).as_ref().unwrap());
            }
        }

        let mut char_indices = value.char_indices();
        match self
            .children
            .get(&char_indices.next().map(|(_index, c)| c).unwrap())
        {
            Some(node) => node.find_alias_return_node(
                &value[char_indices
                    .next()
                    .map(|(index, _c)| index)
                    .unwrap_or_else(|| value.len())..],
            ),
            None => None,
        }
    }

    /// Insert an alias pointing to `sub_graph_node` at all places where `value` exists in the
    /// graph.
    ///
    /// The caller must be sure that no Nodes are removed from the graph after calling this method,
    /// as it may leave some dangling references.
    pub fn add_alias(&mut self, value: &str, sub_graph_node: &'a Node<'a>) {
        // Head recursion.
        for child in self.children.iter_mut().map(|(_c, node)| node) {
            child.add_alias(value, sub_graph_node);
        }

        if let Some(return_node) = self.find_alias_return_node(value) {
            self.aliases.push((sub_graph_node, return_node));
        }
    }

    #[cfg(test)]
    pub fn search(&'a self, word: &str) -> Option<&'a Node<'a>> {
        if word.is_empty() {
            return Some(self);
        }
        let mut char_indices = word.char_indices();
        match self
            .children
            .get(&char_indices.next().map(|(_index, c)| c).unwrap())
        {
            Some(node) => node.search(
                &word[char_indices
                    .next()
                    .map(|(index, _c)| index)
                    .unwrap_or_else(|| word.len())..],
            ),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::node::{Node, NodeType};

    #[test]
    fn as_ptr() {
        let node = Node::new();
        assert!(std::ptr::eq(&node, node.as_ptr() as *const Node));
    }

    #[test]
    fn add_match() {
        let mut node = Node::new();
        node.add_match("foo");

        assert_eq!(
            node.search("foo").unwrap().node_type,
            NodeType::Match("foo")
        );
    }

    #[test]
    fn add_exception() {
        let mut node = Node::new();
        node.add_exception("foo");

        assert_eq!(
            node.search("foo").unwrap().node_type,
            NodeType::Exception("foo")
        );
    }

    #[test]
    fn add_return() {
        let mut node = Node::new();
        node.add_return("foo");

        assert_eq!(node.search("foo").unwrap().node_type, NodeType::Return);
    }

    #[test]
    fn add_alias() {
        let mut node = Node::new();
        node.add_match("foo");

        let alias_node = Node::new();
        node.add_alias("o", &alias_node);

        let first_node = node.search("f").unwrap();
        let second_node = node.search("fo").unwrap();
        let third_node = node.search("foo").unwrap();
        assert_eq!(first_node.aliases.len(), 1);
        assert_eq!(second_node.aliases.len(), 1);
        let (first_node_alias, first_node_return) = first_node.aliases[0];
        let (second_node_alias, second_node_return) = second_node.aliases[0];
        assert!(std::ptr::eq(first_node_alias, &alias_node));
        assert!(std::ptr::eq(first_node_return, second_node));
        assert!(std::ptr::eq(second_node_alias, &alias_node));
        assert!(std::ptr::eq(second_node_return, third_node));
    }
}
