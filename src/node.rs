//! Node type for `WordFilter`'s internal directional graph.
//!
//! The collection of `Node`s contained in a `WordFilter` define the graph upon which the
//! `WordFilter` operates. Edges between the nodes are defined by UTF-8 characters, and traversal
//! through the graph is done by matching on these characters.
//!
//! In addition to the standard parent-child path, subgraphs for both aliases and grapheme clusters
//! can be entered during parsing. These can be both recursive and cyclical.

#![doc(hidden)]

use alloc::vec::Vec;
use core::fmt;

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
    /// This indicates the walker should jump back to the return node, if one exists.
    Return,
}

/// A node within a `WordFilter` graph.
///
/// This struct is only marked public to allow for code generation. It is not considered a part of
/// the public API and should not be relied upon.
///
/// A node has defined children, obtained by matching on characters, as well as subgraphs with
/// their accompanying return nodes.
///
/// Each node also has a [`Type`] defining what kind of node it is.
pub struct Node<'a> {
    /// The node's type.
    pub r#type: Type<'a>,
    /// A function mapping from `char` to child node.
    pub children: fn(char) -> Option<&'a Node<'a>>,
    /// Alias subgraphs.
    pub alias_subgraphs: &'a [(&'a Node<'a>, &'a Node<'a>)],
    /// Grapheme subgraphs.
    pub grapheme_subgraphs: &'a [(&'a Node<'a>, &'a Node<'a>)],
}

impl<'a> Node<'a> {
    /// Convenience method for accessing the `children` field.
    #[inline]
    pub(crate) fn children(&self, c: char) -> Option<&'a Node<'a>> {
        (self.children)(c)
    }
}

/// Custom implementation to handle the potentially cyclical nature of subgraphs.
///
/// References to `Node`s are represented by their address.
impl fmt::Debug for Node<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("type", &self.r#type)
            .field("children", &self.children)
            .field(
                "alias_subgraphs",
                &self
                    .alias_subgraphs
                    .iter()
                    .map(|(subgraph_node, return_node)| {
                        (
                            *subgraph_node as *const Node<'_>,
                            *return_node as *const Node<'_>,
                        )
                    })
                    .collect::<Vec<_>>(),
            )
            .field(
                "grapheme_subgraphs",
                &self
                    .grapheme_subgraphs
                    .iter()
                    .map(|(subgraph_node, return_node)| {
                        (
                            *subgraph_node as *const Node<'_>,
                            *return_node as *const Node<'_>,
                        )
                    })
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}
