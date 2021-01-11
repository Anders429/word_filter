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

use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;

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
    pub children: HashMap<char, Rc<RefCell<Node<'a>>>>,

    /// Any alternative subgraphs that can be traveled from this node.
    ///
    /// These are pairs representing `(sub_graph_node, return_node)`.
    pub aliases: Vec<(Rc<RefCell<Node<'a>>>, Rc<RefCell<Node<'a>>>)>,

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
        Rc::get_mut(self.children
            .entry(char_indices.next().map(|(_index, c)| c).unwrap())
            .or_insert_with(|| Rc::new(RefCell::new(Self::new())))).unwrap()
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

    fn find_alias_return_node(rc_self: &Rc<RefCell<Node<'a>>>, value: &str) -> Option<Rc<RefCell<Node<'a>>>> {
        if value.is_empty() {
            return Some(rc_self.clone());
        }

        let mut char_indices = value.char_indices();
        match rc_self
            .children
            .get(&char_indices.next().map(|(_index, c)| c).unwrap())
        {
            Some(node) => Node::find_alias_return_node(
                node,
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
    pub fn add_alias(rc_self: &mut Rc<RefCell<Node<'a>>>, value: &str, sub_graph_node: &Rc<RefCell<Node<'a>>>) {
        // Head recursion.
        for child in Rc::get_mut(rc_self).unwrap().children.iter_mut().map(|(_c, node)| node) {
            Node::add_alias(child, value, sub_graph_node);
        }

        if let Some(return_node) = Node::find_alias_return_node(rc_self, value) {
            Rc::get_mut(rc_self).unwrap().aliases.push((sub_graph_node.clone(), return_node));
        }
    }

    #[cfg(test)]
    pub fn search(rc_self: &Rc<Node<'a>>, word: &str) -> Option<Rc<Node<'a>>> {
        if word.is_empty() {
            return Some(rc_self.clone());
        }
        let mut char_indices = word.char_indices();
        match rc_self
            .children
            .get(&char_indices.next().map(|(_index, c)| c).unwrap())
        {
            Some(node) => Node::search(rc_self,
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
    use std::rc::Rc;

    #[test]
    fn add_match() {
        let mut node = Node::new();
        node.add_match("foo");

        assert_eq!(
            Node::search(&Rc::new(node), "foo").unwrap().node_type,
            NodeType::Match("foo")
        );
    }

    #[test]
    fn add_exception() {
        let mut node = Node::new();
        node.add_exception("foo");

        assert_eq!(
            Node::search(&Rc::new(node), "foo").unwrap().node_type,
            NodeType::Exception("foo")
        );
    }

    #[test]
    fn add_return() {
        let mut node = Node::new();
        node.add_return("foo");

        assert_eq!(Node::search(&Rc::new(node), "foo").unwrap().node_type, NodeType::Return);
    }

    #[test]
    fn add_alias() {
        let mut node = Rc::new(Node::new());
        Rc::get_mut(&mut node).unwrap().add_match("foo");

        let alias_node = Rc::new(Node::new());
        Node::add_alias(&mut node, "o", &alias_node);

        let first_node = Node::search(&node, "f").unwrap();
        let second_node = Node::search(&node, "fo").unwrap();
        let third_node = Node::search(&node, "foo").unwrap();
        assert_eq!(first_node.aliases.len(), 1);
        assert_eq!(second_node.aliases.len(), 1);
        let first_node_alias = first_node.aliases[0].0.clone();
        let first_node_return = first_node.aliases[0].1.clone();
        let second_node_alias = second_node.aliases[0].0.clone();
        let second_node_return = second_node.aliases[0].1.clone();
        assert!(Rc::ptr_eq(&first_node_alias, &alias_node));
        assert!(Rc::ptr_eq(&first_node_return, &second_node));
        assert!(Rc::ptr_eq(&second_node_alias, &alias_node));
        assert!(Rc::ptr_eq(&second_node_return, &third_node));
    }
}
