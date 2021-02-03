//! Pointer type for `WordFilter`'s internal searching.
//!
//! `Pointer` provides an efficient way for the `WordFilter` to search its own directional graph for
//! matches to a given string.
//!
//! Use of a `Pointer` allows for multiple simultaneous searches to all maintain their own context.
//! This allows for splitting of paths at aliases, searching for separators, and searching at
//! different start locations within the string simultaneously.

use crate::node::{self, Node};
use alloc::vec::Vec;
use nested_containment_list::Interval;

/// The current status of the `Pointer`.
///
/// This indicates whether the `Pointer` has reached a `Match` or an `Exception` node.
#[derive(Clone, Debug)]
pub(crate) enum Status<'a> {
    /// Indicates the `Pointer` has found no `Match` or `Exception` nodes yet.
    None,
    /// Indicates the `Pointer` has found a `Match` node containing the stored string.
    Match(&'a str),
    /// Indicates the `Pointer` has found an `Exception` node containing the stored string.
    Exception(&'a str),
}

/// A specialized pointer for traveling through the `WordFilter`'s `Node` graph.
///
/// The `Pointer` keeps track of the current context within the `Node` (as in, the current pointer
/// location, a stack of return nodes, etc.), as well as information about the `Pointer`'s location
/// within the original source string passed into the `WordFilter`.
///
/// In order to progress the `Pointer` forward, the `step()` method is provided, which allows the
/// user to step the `Pointer` through each character in a string.
#[derive(Clone)]
pub(crate) struct Pointer<'a> {
    /// The current node that is being pointed to.
    pub(crate) current_node: &'a Node<'a>,
    /// A stack of return nodes (indicating the `Pointer`'s context within subgraphs).
    pub(crate) return_nodes: Vec<&'a Node<'a>>,
    /// This `Pointer`'s current status.
    pub(crate) status: Status<'a>,

    /// The start index within the original source string.
    pub(crate) start: usize,
    /// The length which this `Pointer` has traveled.
    pub(crate) len: usize,
    /// The length where the last `Match` or `Exception` node was found.
    pub(crate) found_len: Option<usize>,

    pub(crate) in_separator: bool,
}

impl<'a> Pointer<'a> {
    /// Creates a new `Pointer` with the provided attributes.
    ///
    /// This also sets `status` to `Status::None` and `found_len` to `None`.
    pub(crate) fn new(
        current_node: &'a Node<'a>,
        return_nodes: Vec<&'a Node<'a>>,
        start: usize,
        len: usize,
        in_separator: bool,
    ) -> Self {
        Self {
            current_node,
            return_nodes,
            status: Status::None,
            start,
            len,
            found_len: None,
            in_separator,
        }
    }

    /// Processes a return node.
    ///
    /// This evaluation is evaluated recursively if there are multiple return nodes. If the node is
    /// not actually a return node, the node is itself returned. This will happen when the final
    /// node in the return chain, which is itself not a return node, is encountered.
    ///
    /// If the node *is* a return node, and the `return_nodes` stack is empty, then `None` is
    /// returned. Otherwise, the new node where the `Pointer` should be located is returned.
    fn evaluate_return_node(&mut self, node: &'a Node<'a>) -> Option<&'a Node<'a>> {
        match node.node_type {
            node::Type::Standard => Some(node),
            node::Type::Return => self
                .return_nodes
                .pop()
                .and_then(|return_node| self.evaluate_return_node(return_node)),
            node::Type::Match(word) => {
                if self.in_separator {
                    self.in_separator = false;
                } else {
                    self.status = Status::Match(word);
                    self.found_len = Some(self.len);
                }
                Some(node)
            }
            node::Type::Exception(word) => {
                if self.in_separator {
                    self.in_separator = false;
                } else {
                    self.status = Status::Exception(word);
                    self.found_len = Some(self.len);
                }
                Some(node)
            }
        }
    }

    /// Step the `Pointer` along the character `c`.
    ///
    /// If the `Pointer` has reached a dead-end, this method returns `false`. Otherwise, it returns
    /// `true` to indicate the `Pointer` is still active in the `WordFilter` graph.
    pub(crate) fn step(&mut self, c: char) -> bool {
        self.current_node = match self.current_node.children.get(&c) {
            Some(node) => match node.node_type {
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
                    self.found_len = Some(self.len);
                    node
                }
                node::Type::Exception(word) => {
                    self.status = Status::Exception(word);
                    self.found_len = Some(self.len);
                    node
                }
            },
            None => return false,
        };
        self.len += 1;
        true
    }
}

/// Define `Pointer` as an interval.
///
/// This defines `start()` and `end()` indicating where the matched word or exception starts and
/// ends.
///
/// Note that this only defines a usable interval if a match was found. If no match was found, there
/// is no usable interval, and the `Pointer` shouldn't be used in a `NestedContainmentList`.
impl Interval<usize> for Pointer<'_> {
    #[inline]
    fn start(&self) -> usize {
        self.start
    }

    #[inline]
    fn end(&self) -> usize {
        self.start + self.found_len.unwrap_or(0) + 1
    }
}

#[cfg(test)]
mod tests {
    use crate::node::Node;
    use crate::pointer::{Pointer, Status};
    use alloc::{vec, vec::Vec};
    use claim::assert_matches;

    #[test]
    fn step() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut pointer = Pointer::new(&node, Vec::new(), 0, 0, false);

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(pointer.step('o'));
        assert!(!pointer.step('o'));
    }

    #[test]
    fn step_match() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut pointer = Pointer::new(&node, Vec::new(), 0, 0, false);

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(pointer.step('o'));

        assert_matches!(pointer.status, Status::Match("foo"));
    }

    #[test]
    fn step_exception() {
        let mut node = Node::new();
        node.add_exception("foo");

        let mut pointer = Pointer::new(&node, Vec::new(), 0, 0, false);

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(pointer.step('o'));

        assert_matches!(pointer.status, Status::Exception("foo"));
    }

    #[test]
    fn step_return() {
        let mut node = Node::new();
        node.add_return("foo");

        let return_node = Node::new();

        let mut pointer = Pointer::new(&node, vec![&return_node], 0, 0, false);

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(pointer.step('o'));

        assert!(core::ptr::eq(pointer.current_node, &return_node));
    }

    #[test]
    fn step_return_no_return_node() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut pointer = Pointer::new(&node, Vec::new(), 0, 0, false);

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(!pointer.step('o'));
    }

    #[test]
    fn step_return_in_separator() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut return_node = Node::new();
        return_node.add_match("");

        let mut pointer = Pointer::new(&node, vec![&return_node], 0, 0, true);

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(pointer.step('o'));

        assert!(core::ptr::eq(pointer.current_node, &return_node));
        assert!(!pointer.in_separator);
        assert_eq!(pointer.found_len, None);
    }

    #[test]
    fn step_return_to_exception() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut return_node = Node::new();
        return_node.add_exception("");

        let mut pointer = Pointer::new(&node, vec![&return_node], 0, 0, false);

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(pointer.step('o'));

        assert!(core::ptr::eq(pointer.current_node, &return_node));
    }

    #[test]
    fn step_return_to_exception_in_separator() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut return_node = Node::new();
        return_node.add_exception("");

        let mut pointer = Pointer::new(&node, vec![&return_node], 0, 0, true);

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(pointer.step('o'));

        assert!(core::ptr::eq(pointer.current_node, &return_node));
        assert!(!pointer.in_separator);
        assert_eq!(pointer.found_len, None);
    }

    #[test]
    fn step_return_twice() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut first_return_node = Node::new();
        first_return_node.add_return("");
        let second_return_node = Node::new();

        let mut pointer = Pointer::new(
            &node,
            vec![&second_return_node, &first_return_node],
            0,
            0,
            false,
        );

        assert!(pointer.step('f'));
        assert!(pointer.step('o'));
        assert!(pointer.step('o'));

        assert!(core::ptr::eq(pointer.current_node, &second_return_node));
    }
}
