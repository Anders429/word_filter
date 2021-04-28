//! Node type for `WordFilter`'s internal directional graph.
//!
//! The graph defined by these Nodes is basically a Trie with a few extra attributes. Edges between
//! nodes are defined by characters (UTF-8), and traversal through the graph is done through those
//! characters.
//!
//! In addition to the standard parent-child path, aliases can also be represented as references to
//! other subgraphs. Those subgraphs may end in Return nodes, linking the path back to the
//! supergraph.
//!
//! Each node also has a `Type`, identifying what kind of Node it is.
//!
//! `Node`s implement `!Unpin`, meaning they are, essentially, pinnable. This is necessary due to
//! their self-referential nature. If a `Node` exists that is referenced by any other `Node` (which
//! is basically every node besides `root` and `separator_root`), it should be pinned in memory
//! using `Pin`. After being pinned, great care should be taken when mutating `Node`s, since moving
//! the values will result in invalidating any references to that `Node`. Most `unsafe` calls within
//! the code are dedicated to upholding that invariant.

use alloc::{borrow::ToOwned, boxed::Box, string::String, vec, vec::Vec};
use core::{fmt, marker::PhantomPinned, pin::Pin};
use debug_unreachable::debug_unreachable;
use hashbrown::HashMap;
use unicode_segmentation::UnicodeSegmentation;

/// The different possible node variants.
#[derive(Debug)]
pub(crate) enum Type {
    /// A standard pathway node.
    Standard,
    /// This node indicates a match.
    ///
    /// When traveling along a node path, if a match node is encountered that means a filtered word
    /// is contained in the source string.
    Match(String),
    /// This node indicates an exception.
    ///
    /// When traveling along a node path, if an exception node is encountered that means an
    /// exception word is contained in the source string. If any matches are found within the same
    /// character window they should be ignored.
    Exception(String),
    /// A return pathway node.
    ///
    /// This indicates the walker should jump back to the return node, if one exists.
    Return,
}

/// A Trie structure node.
///
/// It represents a directional graph with character edges. Each Node has defined children, as well
/// as possible alias subgraphs to be traveled on as well.
///
/// Each Node also has a `node_type`, defining what kind of node it is. These are useful if the user
/// wishes to know whether they are at a match, an exception, or perhaps a subgraph return.
pub(crate) struct Node<'a> {
    /// All children Nodes, keyed by character edges.
    pub(crate) children: HashMap<char, Pin<Box<Node<'a>>>>,

    /// Any alternative subgraphs that can be traveled from this node.
    ///
    /// These are pairs representing `(sub_graph_node, return_node)`.
    pub(crate) aliases: Vec<(&'a Node<'a>, &'a Node<'a>)>,

    /// The type of node.
    pub(crate) node_type: Type,

    /// Grapheme subgraphs.
    ///
    /// These values are owned by this Node. They are tuples of `(sub_graph_node, return_node)`.
    pub(crate) grapheme_subgraphs: Vec<(Node<'a>, Node<'a>)>,

    /// Mark as !Unpin.
    pub(crate) _pin: PhantomPinned,
}

impl<'a> Node<'a> {
    /// Creates a new Standard node.
    ///
    /// All internal fields are initialized to be empty.
    pub(crate) fn new() -> Self {
        Self {
            children: HashMap::new(),
            aliases: Vec::new(),
            node_type: Type::Standard,
            grapheme_subgraphs: Vec::new(),
            _pin: PhantomPinned,
        }
    }

    /// Recursively add a path through the characters in `word`, ending with a node of type
    /// `node_type`.
    ///
    /// If the exact path already exists ending in a different `node::Type`, then the previous type
    /// is preserved.
    fn add_path(&mut self, word: &str, node_type: Type) {
        if word.is_empty() {
            if match self.node_type {
                Type::Standard => true,
                _ => false,
            } {
                self.node_type = node_type;
            }
            return;
        }

        let mut graphemes = word.graphemes(true);
        let grapheme = match graphemes.next() {
            Some(g) => g,
            None => unsafe {
                // SAFETY; We guaranteed above that `word` is non-empty, and therefore
                // `graphemes.next()` will always return a value.
                debug_unreachable!()
            },
        };
        if grapheme.chars().count() > 1 {
            let mut subgraph_node = Self::new();
            subgraph_node.add_path_ignoring_graphemes(grapheme, Type::Return);

            let mut return_node = Self::new();
            return_node.add_path(graphemes.as_str(), node_type);

            self.grapheme_subgraphs.push((subgraph_node, return_node));
        } else {
            let mut chars = word.chars();
            unsafe {
                self.children
                    .entry(match chars.next() {
                        Some(c) => c,
                        None => {
                            // SAFETY; We guaranteed above that `word` is non-empty, and therefore
                            // `chars.next()` will always return a value.
                            debug_unreachable!()
                        }
                    })
                    .or_insert_with(|| Box::pin(Self::new()))
                    .as_mut()
                    // SAFETY: Adding a path to a `Node` will not move the `Node`. Therefore, this
                    // mutation of the `Node` will uphold pin invariants.
                    .get_unchecked_mut()
                    .add_path(chars.as_str(), node_type);
            }
        }
    }

    fn add_path_ignoring_graphemes(&mut self, word: &str, node_type: Type) {
        if word.is_empty() {
            if match self.node_type {
                Type::Standard => true,
                _ => false,
            } {
                self.node_type = node_type;
            }
            return;
        }

        let mut chars = word.chars();
        unsafe {
            self.children
                .entry(match chars.next() {
                    Some(c) => c,
                    None => {
                        // SAFETY; We guaranteed above that `word` is non-empty, and therefore
                        // `chars.next()` will always return a value.
                        debug_unreachable!()
                    }
                })
                .or_insert_with(|| Box::pin(Self::new()))
                .as_mut()
                // SAFETY: Adding a path to a `Node` will not move the `Node`. Therefore, this
                // mutation of the `Node` will uphold pin invariants.
                .get_unchecked_mut()
                .add_path_ignoring_graphemes(chars.as_str(), node_type);
        }
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as a Match.
    pub(crate) fn add_match(&mut self, word: &str) {
        self.add_path(word, Type::Match(word.to_owned()));
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as an Exception.
    pub(crate) fn add_exception(&mut self, word: &str) {
        self.add_path(word, Type::Exception(word.to_owned()));
    }

    /// Add Nodes and char edges representing `word`, and mark the final Node as a Return.
    pub(crate) fn add_return(&mut self, word: &str) {
        self.add_path(word, Type::Return);
    }

    fn consume_chars_until_return_node<'b>(&self, value: &'b str) -> Option<&'b str> {
        if let Type::Return = self.node_type {
            return Some(value);
        }

        if value.is_empty() {
            return None;
        }

        let mut chars = value.chars();
        self.children
            .get(&match chars.next() {
                Some(c) => c,
                None => unsafe {
                    // SAFETY: `value` is verified above to be non-empty. Therefore, `chars` will always
                    // return a value on `next()`.
                    debug_unreachable!()
                },
            })
            .and_then(|node| node.consume_chars_until_return_node(chars.as_str()))
    }

    /// Finds the return node for an alias, if one exists.
    ///
    /// Travels along the node path using `value`, until it either reaches a dead end or consumes
    /// all of `value`. If a dead end is reached, `None` is returned instead.
    fn find_alias_return_nodes(&self, value: &str) -> vec::IntoIter<&'a Node<'a>> {
        if value.is_empty() {
            return unsafe {
                // SAFETY: The obtained reference to a Node is self-referential within the
                // WordFilter struct. The only reason this conversion from reference to pointer and
                // back again is necessary is to make the reference lifetime-agnostic to allow the
                // self-reference. This is safe, because every Node owned in the graph by the
                // WordFilter is pinned in place in memory, meaning it will only ever move when the
                // WordFilter is dropped. Therefore, this reference will be valid for as long as it
                // is used by the WordFilter.
                vec![&*(self as *const Node<'_>)].into_iter()
            };
        }

        let mut return_nodes = Vec::new();

        // Direct children.
        let mut chars = value.chars();
        self.children
            .get(&match chars.next() {
                Some(c) => c,
                None => unsafe {
                    // SAFETY: `value` is verified above to be non-empty. Therefore, `chars` will
                    // always return a value on `next()`.
                    debug_unreachable!()
                },
            })
            .into_iter()
            .for_each(|node| {
                return_nodes.extend(node.find_alias_return_nodes(chars.as_str()));
            });

        // Grapheme subgraphs.
        for (grapheme_subgraph_node, grapheme_return_node) in &self.grapheme_subgraphs {
            grapheme_subgraph_node
                .consume_chars_until_return_node(value)
                .into_iter()
                .for_each(|consumed_value| {
                    return_nodes
                        .extend(grapheme_return_node.find_alias_return_nodes(consumed_value))
                });
        }

        return_nodes.into_iter()
    }

    /// Insert an alias pointing to `sub_graph_node` at all places where `value` exists in the
    /// graph.
    ///
    /// The caller must be sure that no Nodes are removed from the graph after calling this method,
    /// as it may leave some dangling references.
    pub(crate) fn add_alias(&mut self, value: &str, sub_graph_node: &'a Node<'a>) {
        // Head recursion.
        for child in self.children.iter_mut().map(|(_c, node)| node) {
            unsafe {
                // SAFETY: Adding an alias to a `Node` will not move the `Node`. Therefore, this
                // mutation of the `Node` will uphold pin invariants.
                child
                    .as_mut()
                    .get_unchecked_mut()
                    .add_alias(value, sub_graph_node);
            }
        }

        for return_node in self.find_alias_return_nodes(value) {
            self.aliases.push((sub_graph_node, return_node));
        }
    }

    /// A test-only method used to search directly from a Node.
    ///
    /// In production, the actual traversal through the graph is handled by a Walker.
    #[cfg(test)]
    pub(crate) fn search(&'a self, word: &str) -> Option<&'a Node<'a>> {
        if word.is_empty() {
            return Some(self);
        }

        let mut chars = word.chars();
        self.children
            .get(&chars.next().unwrap())
            .and_then(|node| node.search(chars.as_str()))
    }
}

impl fmt::Debug for Node<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("children", &self.children)
            .field(
                "aliases",
                &self
                    .aliases
                    .iter()
                    .map(|(subgraph_node, return_node)| {
                        (
                            *subgraph_node as *const Node<'_>,
                            *return_node as *const Node<'_>,
                        )
                    })
                    .collect::<Vec<_>>(),
            )
            .field("node_type", &self.node_type)
            .field("grapheme_subgraphs", &self.grapheme_subgraphs)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::node::{Node, Type};
    use alloc::format;
    use claim::assert_matches;

    #[test]
    fn add_match() {
        let mut node = Node::new();
        node.add_match("foo");

        assert_matches!(&node.search("foo").unwrap().node_type, Type::Match(ref value) if value == "foo");
    }

    #[test]
    fn add_exception() {
        let mut node = Node::new();
        node.add_exception("foo");

        assert_matches!(
            &node.search("foo").unwrap().node_type,
            Type::Exception(ref value) if value == "foo"
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

    #[test]
    fn debug() {
        let node = Node::new();

        assert_eq!(
            format!("{:?}", node),
            "Node { children: {}, aliases: [], node_type: Standard, grapheme_subgraphs: [] }"
        )
    }
}
