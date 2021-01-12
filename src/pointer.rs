//! Pointer type for `WordFilter`'s internal searching.
//!
//! `Pointer` provides an efficient way for the `WordFilter` to search its own directional graph for
//! matches to a given string.
//!
//! Use of a `Pointer` allows for multiple simultaneous searches to all maintain their own context.
//! This allows for splitting of paths at aliases, searching for separators, and searching at
//! different start locations within the string simultaneously.

use crate::node::{Node, NodeType};

/// The current status of the `Pointer`.
///
/// This indicates whether the `Pointer` has reached a `Match` or an `Exception` node.
#[derive(Clone, Debug, PartialEq)]
pub enum PointerStatus<'a> {
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
pub struct Pointer<'a> {
    /// The current node that is being pointed to.
    pub current_node: &'a Node<'a>,
    /// A stack of return nodes (indicating the `Pointer`'s context within subgraphs).
    pub return_nodes: Vec<&'a Node<'a>>,
    /// This `Pointer`'s current status.
    pub status: PointerStatus<'a>,

    /// The start index within the original source string.
    pub start: usize,
    /// The length which this `Pointer` has traveled.
    pub len: usize,
    /// The length where the last `Match` or `Exception` node was found.
    pub found_len: Option<usize>,
}

impl<'a> Pointer<'a> {
    /// Creates a new `Pointer` with the provided attributes.
    ///
    /// This also sets `status` to `PointerStatus::None` and `found_len` to `None`.
    pub fn new(
        current_node: &'a Node<'a>,
        return_nodes: Vec<&'a Node<'a>>,
        start: usize,
        len: usize,
    ) -> Self {
        Self {
            current_node,
            return_nodes,
            status: PointerStatus::None,
            start,
            len,
            found_len: None,
        }
    }

    /// Processes a return node.
    ///
    /// This evaluation is very conservative. If the node is not actually a return node, the node
    /// is itself returned.
    ///
    /// If the node *is* a return node, and the `return_nodes` stack is empty, then `None` is
    /// returned. Otherwise, the new node where the `Pointer` should be located is returned.
    fn evaluate_return_node(&mut self, node: &'a Node<'a>) -> Option<&'a Node<'a>> {
        match node.node_type {
            NodeType::Standard => Some(node),
            NodeType::Return => {
                if let Some(return_node) = self.return_nodes.pop() {
                    self.evaluate_return_node(return_node)
                } else {
                    None
                }
            }
            NodeType::Match(word) => {
                self.status = PointerStatus::Match(word);
                self.found_len = Some(self.len);
                Some(node)
            }
            NodeType::Exception(word) => {
                self.status = PointerStatus::Exception(word);
                self.found_len = Some(self.len);
                Some(node)
            }
        }
    }

    /// Step the `Pointer` along the character `c`.
    ///
    /// If the `Pointer` has reached a dead-end, this method returns `false`. Otherwise, it returns
    /// `true` to indicate the `Pointer` is still active in the `WordFilter` graph.
    pub fn step(&mut self, c: &char) -> bool {
        self.current_node = match self.current_node.children.get(c) {
            Some(node) => match node.node_type {
                NodeType::Standard => node,
                NodeType::Return => {
                    if let Some(return_node) = self.evaluate_return_node(node) {
                        return_node
                    } else {
                        return false;
                    }
                }
                NodeType::Match(word) => {
                    self.status = PointerStatus::Match(word);
                    self.found_len = Some(self.len);
                    node
                }
                NodeType::Exception(word) => {
                    self.status = PointerStatus::Exception(word);
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

#[cfg(test)]
mod tests {
    use crate::node::Node;
    use crate::pointer::{Pointer, PointerStatus};

    #[test]
    fn step() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut pointer = Pointer::new(&node, Vec::new(), 0, 0);

        assert!(pointer.step(&'f'));
        assert!(pointer.step(&'o'));
        assert!(pointer.step(&'o'));
        assert!(!pointer.step(&'o'));
    }

    #[test]
    fn step_match() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut pointer = Pointer::new(&node, Vec::new(), 0, 0);

        assert!(pointer.step(&'f'));
        assert!(pointer.step(&'o'));
        assert!(pointer.step(&'o'));

        assert_eq!(pointer.status, PointerStatus::Match("foo"));
    }

    #[test]
    fn step_exception() {
        let mut node = Node::new();
        node.add_exception("foo");

        let mut pointer = Pointer::new(&node, Vec::new(), 0, 0);

        assert!(pointer.step(&'f'));
        assert!(pointer.step(&'o'));
        assert!(pointer.step(&'o'));

        assert_eq!(pointer.status, PointerStatus::Exception("foo"));
    }

    #[test]
    fn step_return() {
        let mut node = Node::new();
        node.add_return("foo");

        let return_node = Node::new();

        let mut pointer = Pointer::new(&node, vec![&return_node], 0, 0);

        assert!(pointer.step(&'f'));
        assert!(pointer.step(&'o'));
        assert!(pointer.step(&'o'));

        assert!(std::ptr::eq(pointer.current_node, &return_node));
    }

    #[test]
    fn step_return_no_return_node() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut pointer = Pointer::new(&node, Vec::new(), 0, 0);

        assert!(pointer.step(&'f'));
        assert!(pointer.step(&'o'));
        assert!(!pointer.step(&'o'));
    }
}
