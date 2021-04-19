//! Walker for [`WordFilter`]'s internal searching.
//!
//! [`Walker`] provides an efficient way for the `WordFilter` to search its own directional graph for
//! matches to a given string.
//!
//! Use of a `Walker` allows for multiple simultaneous searches to all maintain their own context.
//! This allows for splitting of paths at aliases, searching for separators, and searching at
//! different start locations within the string simultaneously.
//!
//! [`WordFilter`]: crate::WordFilter

use crate::node::{self, Node};
use alloc::vec::Vec;
use core::{
    ops::{Bound, RangeBounds},
    ptr,
};

/// The current status of the `Walker`.
///
/// This indicates whether the `Walker` has reached a `Match` or an `Exception` node.
#[derive(Clone, Debug)]
pub(crate) enum Status<'a> {
    /// Indicates the `Walker` has found no `Match` or `Exception` nodes yet.
    None,
    /// Indicates the `Walker` has found a `Match` node containing the stored string.
    Match(&'a str),
    /// Indicates the `Walker` has found an `Exception` node containing the stored string.
    Exception(&'a str),
}

#[derive(Clone)]
pub(crate) enum NodeWithSubgraphContext<'a> {
    InSubgraph(&'a Node<'a>),
    NotInSubgraph(&'a Node<'a>),
}

/// A specialized walker for traveling through the `WordFilter`'s `Node` graph.
///
/// The `Walker` keeps track of the current context within the `Node` (as in, the current walker
/// location, a stack of return nodes, etc.), as well as information about the `Walker`'s location
/// within the original source string passed into the `WordFilter`.
///
/// In order to progress the `Walker` forward, the `step()` method is provided, which allows the
/// user to step the `Walker` through each character in a string.
#[derive(Clone)]
pub(crate) struct Walker<'a> {
    /// The current node.
    pub(crate) current_node: &'a Node<'a>,
    /// A stack of return nodes (indicating the `Walker`'s context within subgraphs).
    pub(crate) return_nodes: Vec<&'a Node<'a>>,
    /// This `Walker`'s current status.
    pub(crate) status: Status<'a>,

    /// The start index within the original source string.
    pub(crate) start: usize,
    /// The length which this `Walker` has traveled.
    pub(crate) len: usize,
    /// The end index where the last `Match` or `Exception` node was found.
    pub(crate) found_end: Option<usize>,

    /// Indicates whether the walker is operating within a separator.
    ///
    /// This allows exclusion of trailing separator characters from matches and exceptions.
    pub(crate) in_separator: bool,

    pub(crate) repeated_character_stack: Vec<Option<&'a Node<'a>>>,

    pub(crate) callbacks: Vec<NodeWithSubgraphContext<'a>>,
    pub(crate) targets: Vec<NodeWithSubgraphContext<'a>>,
    pub(crate) new_walkers: Vec<Walker<'a>>,
}

impl<'a> Walker<'a> {
    /// Creates a new `Walker` with the provided attributes.
    ///
    /// This also sets `status` to `Status::None` and `found_len` to `None`.
    pub(crate) fn new(
        current_node: &'a Node<'a>,
        return_nodes: Vec<&'a Node<'a>>,
        start: usize,
        len: usize,
        in_separator: bool,
        repeated_character_stack: Vec<Option<&'a Node<'a>>>,
    ) -> Self {
        Self {
            current_node,
            return_nodes,
            status: Status::None,
            start,
            len,
            found_end: None,
            in_separator,
            repeated_character_stack,
            callbacks: Vec::new(),
            targets: Vec::new(),
            new_walkers: Vec::new(),
        }
    }

    /// Processes a return node.
    ///
    /// This evaluation is evaluated recursively if there are multiple return nodes. If the node is
    /// not actually a return node, the node is itself returned. This will happen when the final
    /// node in the return chain, which is itself not a return node, is encountered.
    ///
    /// If the node *is* a return node, and the `return_nodes` stack is empty, then `None` is
    /// returned. Otherwise, the new node where the `Walker` should be located is returned.
    fn evaluate_return_node(&mut self, node: &'a Node<'a>) -> Option<&'a Node<'a>> {
        match node.node_type {
            node::Type::Standard => Some(node),
            node::Type::Return => {
                if let Some(target) = self.targets.pop() {}
                self.return_nodes
                    .pop()
                    .and_then(|return_node| self.evaluate_return_node(return_node))
            }
            node::Type::Match(word) => {
                if self.in_separator {
                    self.in_separator = false;
                } else {
                    self.status = Status::Match(word);
                    self.found_end = Some(self.start + self.len);
                }
                Some(node)
            }
            node::Type::Exception(word) => {
                if self.in_separator {
                    self.in_separator = false;
                } else {
                    self.status = Status::Exception(word);
                    self.found_end = Some(self.start + self.len);
                }
                Some(node)
            }
        }
    }

    /// Step the `Walker` along the character `c`.
    ///
    /// If the `Walker` has reached a dead-end, this method returns `false`. Otherwise, it returns
    /// `true` to indicate the `Walker` is still active in the `WordFilter` graph.
    pub(crate) fn step(&mut self, c: char) -> bool {
        self.current_node = match self.current_node.children.get(&c) {
            Some(node) => {
                match self.repeated_character_stack.last().cloned().flatten() {
                    Some(repeated_target_node) => {
                        extern crate std;
                        std::println!("{}", c);
                        std::println!("{:p}", node.as_ref().get_ref());
                        std::println!("{:p}", repeated_target_node);
                        if !ptr::eq(node.as_ref().get_ref(), repeated_target_node) {
                            return false;
                        }
                    }
                    None => {}
                }
                match node.node_type {
                    node::Type::Standard => node,
                    node::Type::Return => {
                        if let Some(return_node) = self.evaluate_return_node(node) {
                            return_node
                        } else {
                            return false;
                        }
                    }
                    node::Type::Match(word) => {
                        self.status = Status::Match(word);
                        self.found_end = Some(self.start + self.len);
                        node
                    }
                    node::Type::Exception(exception) => {
                        self.status = Status::Exception(exception);
                        self.found_end = Some(self.start + self.len);
                        node
                    }
                }
            }
            None => return false,
        };

        self.len += 1;
        if let Some(repeated_character) = self.repeated_character_stack.last_mut() {
            *repeated_character = None;
        }
        extern crate std;
        std::println!("{} passed", c);
        true
    }
}

/// Define `Walker` to have [`RangeBounds`].
///
/// The bounds correspond with the matched word or exception's start and end character positions.
///
/// Note that this only defines a usable interval if a match or exception was found. If nothing was
/// found, there is no usable interval, and the `Walker` shouldn't be used in contexts needing
/// `RangeBounds`.
///
/// [`RangeBounds`]: core::ops::RangeBounds
impl RangeBounds<usize> for Walker<'_> {
    #[inline]
    fn start_bound(&self) -> Bound<&usize> {
        Bound::Included(&self.start)
    }

    #[inline]
    fn end_bound(&self) -> Bound<&usize> {
        Bound::Included(self.found_end.as_ref().unwrap_or(&self.start))
    }
}

#[cfg(test)]
mod tests {
    use crate::node::Node;
    use crate::walker::{Status, Walker};
    use alloc::{vec, vec::Vec};
    use claim::assert_matches;

    #[test]
    fn step() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut walker = Walker::new(&node, Vec::new(), 0, 0, false, vec![None]);

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(walker.step('o'));
        assert!(!walker.step('o'));
    }

    #[test]
    fn step_match() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut walker = Walker::new(&node, Vec::new(), 0, 0, false, vec![None]);

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(walker.step('o'));

        assert_matches!(walker.status, Status::Match("foo"));
    }

    #[test]
    fn step_exception() {
        let mut node = Node::new();
        node.add_exception("foo");

        let mut walker = Walker::new(&node, Vec::new(), 0, 0, false, vec![None]);

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(walker.step('o'));

        assert_matches!(walker.status, Status::Exception("foo"));
    }

    #[test]
    fn step_return() {
        let mut node = Node::new();
        node.add_return("foo");

        let return_node = Node::new();

        let mut walker = Walker::new(&node, vec![&return_node], 0, 0, false, vec![None]);

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(walker.step('o'));

        assert!(core::ptr::eq(walker.current_node, &return_node));
    }

    #[test]
    fn step_return_no_return_node() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut walker = Walker::new(&node, Vec::new(), 0, 0, false, vec![None]);

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(!walker.step('o'));
    }

    #[test]
    fn step_return_in_separator() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut return_node = Node::new();
        return_node.add_match("");

        let mut walker = Walker::new(&node, vec![&return_node], 0, 0, true, vec![None]);

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(walker.step('o'));

        assert!(core::ptr::eq(walker.current_node, &return_node));
        assert!(!walker.in_separator);
        assert_eq!(walker.found_end, None);
    }

    #[test]
    fn step_return_to_exception() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut return_node = Node::new();
        return_node.add_exception("");

        let mut walker = Walker::new(&node, vec![&return_node], 0, 0, false, vec![None]);

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(walker.step('o'));

        assert!(core::ptr::eq(walker.current_node, &return_node));
    }

    #[test]
    fn step_return_to_exception_in_separator() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut return_node = Node::new();
        return_node.add_exception("");

        let mut walker = Walker::new(&node, vec![&return_node], 0, 0, true, vec![None]);

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(walker.step('o'));

        assert!(core::ptr::eq(walker.current_node, &return_node));
        assert!(!walker.in_separator);
        assert_eq!(walker.found_end, None);
    }

    #[test]
    fn step_return_twice() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut first_return_node = Node::new();
        first_return_node.add_return("");
        let second_return_node = Node::new();

        let mut walker = Walker::new(
            &node,
            vec![&second_return_node, &first_return_node],
            0,
            0,
            false,
            vec![None],
        );

        assert!(walker.step('f'));
        assert!(walker.step('o'));
        assert!(walker.step('o'));

        assert!(core::ptr::eq(walker.current_node, &second_return_node));
    }
}
