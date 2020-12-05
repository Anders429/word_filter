use crate::node::{Node, NodeType};

#[derive(Clone, Debug, PartialEq)]
pub enum PointerStatus<'a> {
    None,
    Match(&'a str),
    Exception(&'a str),
}

#[derive(Clone)]
pub struct Pointer<'a> {
    pub current_node: &'a Node<'a>,
    pub return_nodes: Vec<&'a Node<'a>>,
    pub status: PointerStatus<'a>,

    pub start: usize,
    pub len: usize,
    pub found_len: Option<usize>,
}

impl<'a> Pointer<'a> {
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
