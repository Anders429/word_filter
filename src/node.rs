#![doc(hidden)]

use alloc::vec::Vec;
use core::fmt;

#[derive(Debug)]
pub enum Type<'a> {
    Standard,
    Match(&'a str),
    Exception(&'a str),
    Return,
}

pub struct Node<'a> {
    pub r#type: Type<'a>,
    pub children: fn(char) -> Option<&'a Node<'a>>,
    pub alias_subgraphs: &'a [(&'a Node<'a>, &'a Node<'a>)],
    pub grapheme_subgraphs: &'a [(&'a Node<'a>, &'a Node<'a>)],
}

impl<'a> Node<'a> {
    #[inline]
    pub(crate) fn children(&self, c: char) -> Option<&'a Node<'a>> {
        (self.children)(c)
    }
}

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
