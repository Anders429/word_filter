//! Node type for `WordFilter`'s internal directional graph.
//!
//! The graph defined by these Nodes is basically a Trie with a few extra attributes. Edges between
//! nodes are defined by characters (UTF-8), and traversal through the graph is done through those
//! characters.

//! In addition to the standard parent-child path, aliases can also be represented as references to
//! other subgraphs. Those subgraphs may end in Return nodes, linking the path back to the
//! supergraph.
//!
//! Each node also has a `Type`, identifying what kind of Node it is.

use alloc::{boxed::Box, vec::Vec};
use core::pin::Pin;
use hashbrown::HashMap;

/// The different possible node variants.
#[derive(Debug)]
pub enum Type<'a> {
    /// A standard pathway node.
    Standard,
    /// This node indicates a match.
    ///
    /// When traveling along a node path, if a match node is encountered that means a filtered word
    /// is contained in the source string.
    Match(&'a str),
    /// This node indicates an exception.
    ///
    /// When traveling along a node path, if an exception node is encountered that means an
    /// exception word is contained in the source string. If any matches are found within the same
    /// character window they should be ignored.
    Exception(&'a str),
    /// A return pathway node.
    ///
    /// This indicates the pointer should jump back to the return node, if one exists.
    Return,
}

/// A Trie structure node.
///
/// It represents a directional graph with character edges. Each Node has defined children, as well
/// as possible alias subgraphs to be traveled on as well.
///
/// Each Node also has a `node_type`, defining what kind of node it is. These are useful if the user
/// wishes to know whether they are at a match, an exception, or perhaps a subgraph return.
pub struct Node<'a> {
    /// All children Nodes, keyed by character edges.
    pub children: HashMap<char, Pin<Box<Node<'a>>>>,

    /// Any alternative subgraphs that can be traveled from this node.
    ///
    /// These are pairs representing `(sub_graph_node, return_node)`.
    pub aliases: Vec<(&'a Node<'a>, &'a Node<'a>)>,

    /// The type of node.
    pub node_type: Type<'a>,
}

impl<'a> Node<'a> {
    /// Creates a new Standard node.
    ///
    /// All internal fields are initialized to be empty.
    pub fn new() -> Self {
        Self {
            children: HashMap::new(),
            aliases: Vec::new(),
            node_type: Type::Standard,
        }
    }

    fn add_path(&mut self, word: &str, node_type: Type<'a>) {
        if word.is_empty() {
            if match self.node_type {
                Type::Standard => true,
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
                    .map_or_else(|| word.len(), |(index, _c)| index)..],
                node_type,
            );
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as a Match.
    pub fn add_match(&mut self, word: &'a str) {
        self.add_path(word, Type::Match(word));
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as an Exception.
    pub fn add_exception(&mut self, word: &'a str) {
        self.add_path(word, Type::Exception(word));
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as a Return.
    pub fn add_return(&mut self, word: &str) {
        self.add_path(word, Type::Return);
    }

    /// Finds the return node for an alias, if one exists.
    ///
    /// Travels along the node path using `value`, until it either reaches a dead end or consumes
    /// all of `value`. If a dead end is reached, `None` is returned instead.
    fn find_alias_return_node(&self, value: &str) -> Option<&'a Node<'a>> {
        if value.is_empty() {
            unsafe {
                // SAFETY: The obtained reference to a Node is self-referential within the
                // WordFilter struct. The only reason this conversion from reference to pointer and
                // back again is necessary is to make the reference lifetime-agnostic to allow the
                // self-reference. This is safe, because every Node owned in the graph by the
                // WordFilter is pinned in place in memory, meaning it will only ever move when the
                // WordFilter is dropped. Therefore, this reference will be valid for as long as it
                // is used by the WordFilter.
                return Some(&*(self as *const Node));
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
                    .map_or_else(|| value.len(), |(index, _c)| index)..],
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

    /// A test-only method used to search directly from a Node.
    ///
    /// In production, the actual traversal through the graph is handled by a Pointer.
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
    use crate::node::{Node, Type};
    use claim::assert_matches;

    #[test]
    fn add_match() {
        let mut node = Node::new();
        node.add_match("foo");

        assert_matches!(&node.search("foo").unwrap().node_type, Type::Match("foo"));
    }

    #[test]
    fn add_exception() {
        let mut node = Node::new();
        node.add_exception("foo");

        assert_matches!(
            &node.search("foo").unwrap().node_type,
            Type::Exception("foo")
        );
    }

    #[test]
    fn add_return() {
        let mut node = Node::new();
        node.add_return("foo");

        assert_matches!(&node.search("foo").unwrap().node_type, Type::Return);
    }

    #[test]
    fn add_alias() {
        let alias_node = Node::new();
        let mut node = Node::new();
        node.add_match("foo");

        node.add_alias("o", &alias_node);

        let first_node = node.search("f").unwrap();
        let second_node = node.search("fo").unwrap();
        let third_node = node.search("foo").unwrap();
        assert_eq!(first_node.aliases.len(), 1);
        assert_eq!(second_node.aliases.len(), 1);
        let (first_node_alias, first_node_return) = first_node.aliases[0];
        let (second_node_alias, second_node_return) = second_node.aliases[0];
        assert!(core::ptr::eq(first_node_alias, &alias_node));
        assert!(core::ptr::eq(first_node_return, second_node));
        assert!(core::ptr::eq(second_node_alias, &alias_node));
        assert!(core::ptr::eq(second_node_return, third_node));
    }

    #[test]
    fn cannot_add_to_nonstandard_node() {
        let mut node = Node::new();
        node.add_return("foo");
        node.add_match("foo");

        assert_matches!(&node.search("foo").unwrap().node_type, Type::Return);
    }
}
