use crate::node::{self, Node};
use alloc::vec::{self, Vec};
use by_address::ByAddress;
use core::{
    fmt,
    ops::{Bound, RangeBounds},
    ptr,
};
use hashbrown::HashSet;

/// The current status of the `Walker`.
///
/// This indicates whether the `Walker` has reached a `Match` or an `Exception` node.
#[derive(Clone, Debug)]
pub(crate) enum Status<'a> {
    /// Indicates the `Walker` has found no `Match` or `Exception` nodes yet.
    None,
    /// Indicates the `Walker` has found a `Match` node containing the end index and the stored
    /// string.
    Match(usize, &'a str),
    /// Indicates the `Walker` has found an `Exception` node containing the end index and the stored
    /// string.
    Exception(usize, &'a str),
}

#[derive(Clone)]
pub(crate) enum ContextualizedNode<'a> {
    InDirectPath(&'a Node<'a>),
    InSubgraph(&'a Node<'a>),
}

impl fmt::Debug for ContextualizedNode<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ContextualizedNode::InDirectPath(node) => f
                .debug_tuple("InDirectPath")
                .field(&(*node as *const Node))
                .finish(),
            ContextualizedNode::InSubgraph(node) => f
                .debug_tuple("InSubgraph")
                .field(&(*node as *const Node))
                .finish(),
        }
    }
}

#[derive(Clone)]
pub(crate) struct Walker<'a> {
    pub(crate) node: &'a Node<'a>,
    pub(crate) status: Status<'a>,

    pub(crate) start: usize,
    len: usize,

    pub(crate) in_separator: bool,

    pub(crate) returns: Vec<&'a Node<'a>>,
    pub(crate) callbacks: Vec<ContextualizedNode<'a>>,
    targets: Vec<ContextualizedNode<'a>>,
}

impl<'a> Walker<'a> {
    pub(crate) fn branch_to_aliases(
        &self,
        visited: &mut HashSet<ByAddress<&Node<'a>>>,
    ) -> vec::IntoIter<Walker<'a>> {
        let mut result = Vec::new();

        for (alias_node, return_node) in &self.node.aliases {
            if visited.contains(&ByAddress(alias_node)) {
                continue;
            }
            let mut alias_walker = self.clone();
            alias_walker.node = alias_node;
            alias_walker.returns.push(return_node);
            alias_walker.in_separator = false;

            visited.insert(ByAddress(alias_node));
            result.extend(alias_walker.branch_to_aliases(visited));
            visited.remove(&ByAddress(alias_node));

            result.push(alias_walker);
        }

        result.into_iter()
    }

    fn evaluate_return_node(&mut self) -> Result<vec::IntoIter<Walker<'a>>, ()> {
        let mut result = Vec::new();

        match self.node.node_type {
            node::Type::Standard => {}
            node::Type::Return => {
                self.node = match self.returns.pop() {
                    Some(node) => node,
                    None => return Err(()),
                };

                if let Some(ContextualizedNode::InSubgraph(target_node)) = self.targets.last() {
                    if !ptr::eq(self.node, *target_node) {
                        return Err(());
                    }
                    self.targets.pop();
                }
                if let Some(ContextualizedNode::InSubgraph(callback_node)) = self.callbacks.last() {
                    let mut callback_walker = self.clone();
                    callback_walker.node = callback_node;
                    callback_walker.len += 1;

                    result.extend(
                        callback_walker
                            .branch_to_aliases(&mut HashSet::new())
                            .into_iter()
                            .map(|mut walker| {
                                walker
                                    .targets
                                    .push(ContextualizedNode::InSubgraph(self.node));
                                walker
                                    .callbacks
                                    .push(ContextualizedNode::InSubgraph(callback_node));
                                walker
                            }),
                    );

                    callback_walker
                        .targets
                        .push(ContextualizedNode::InDirectPath(self.node));
                    callback_walker
                        .callbacks
                        .push(ContextualizedNode::InDirectPath(callback_node));
                    result.push(callback_walker);

                    self.callbacks.pop();
                }

                result.extend(self.evaluate_return_node()?);
            }
            node::Type::Match(word) => {
                if self.in_separator {
                    self.in_separator = false;
                } else {
                    self.status = Status::Match(self.start + self.len + 1, word);
                }
            }
            node::Type::Exception(exception) => {
                if self.in_separator {
                    self.in_separator = false;
                } else {
                    self.status = Status::Exception(self.start + self.len + 1, exception);
                }
            }
        }

        Ok(result.into_iter())
    }

    pub(crate) fn step(&mut self, c: char) -> Result<vec::IntoIter<Walker<'a>>, ()> {
        let mut branches = Vec::new();

        match self.node.children.get(&c) {
            Some(node) => {
                match node.node_type {
                    node::Type::Return => {}
                    _ => {
                        if let Some(ContextualizedNode::InDirectPath(target_node)) =
                            self.targets.last()
                        {
                            if !ptr::eq(node.as_ref().get_ref(), *target_node) {
                                return Err(());
                            }
                            self.targets.pop();
                        }
                        if let Some(ContextualizedNode::InDirectPath(callback_node)) =
                            self.callbacks.last()
                        {
                            let mut callback_walker = self.clone();
                            callback_walker.node = callback_node;
                            callback_walker.len += 1;

                            branches.extend(
                                callback_walker
                                    .branch_to_aliases(&mut HashSet::new())
                                    .into_iter()
                                    .map(|mut walker| {
                                        walker.targets.push(ContextualizedNode::InSubgraph(node));
                                        walker
                                            .callbacks
                                            .push(ContextualizedNode::InSubgraph(callback_node));
                                        walker
                                    }),
                            );

                            callback_walker
                                .targets
                                .push(ContextualizedNode::InDirectPath(node));
                            callback_walker
                                .callbacks
                                .push(ContextualizedNode::InDirectPath(callback_node));
                            branches.push(callback_walker);

                            self.callbacks.pop();
                        }
                    }
                }
                self.node = node;
                match self.node.node_type {
                    node::Type::Standard => {}
                    node::Type::Return => {
                        branches.extend(self.evaluate_return_node()?);
                    }
                    node::Type::Match(word) => {
                        self.status = Status::Match(self.start + self.len + 1, word);
                    }
                    node::Type::Exception(exception) => {
                        self.status = Status::Exception(self.start + self.len + 1, exception);
                    }
                }
            }
            None => return Err(()),
        };
        self.len += 1;

        Ok(branches.into_iter())
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
        match self.status {
            Status::None => Bound::Excluded(&self.start),
            Status::Match(ref end, _) => Bound::Excluded(end),
            Status::Exception(ref end, _) => Bound::Included(end),
        }
    }
}

impl fmt::Debug for Walker<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Walker")
            .field("node", &(self.node as *const Node))
            .field("status", &self.status)
            .field("start", &self.start)
            .field("len", &self.len)
            .field("in_separator", &self.in_separator)
            .field(
                "returns",
                &self.returns
                    .iter()
                    .map(|node| *node as *const Node)
                    .collect::<Vec<_>>(),
            )
            .field("callbacks", &self.callbacks)
            .field("targets", &self.targets)
            .finish()
    }
}

pub(crate) struct WalkerBuilder<'a> {
    node: &'a Node<'a>,
    status: Status<'a>,

    start: usize,
    len: usize,

    in_separator: bool,

    returns: Vec<&'a Node<'a>>,
    callbacks: Vec<ContextualizedNode<'a>>,
    targets: Vec<ContextualizedNode<'a>>,
}

impl<'a> WalkerBuilder<'a> {
    #[inline]
    #[must_use]
    pub(crate) fn new(node: &'a Node<'a>) -> Self {
        Self {
            node: node,
            status: Status::None,

            start: 0,
            len: 0,

            in_separator: false,

            returns: Vec::new(),
            callbacks: Vec::new(),
            targets: Vec::new(),
        }
    }

    #[inline]
    pub(crate) fn status(mut self, status: Status<'a>) -> Self {
        self.status = status;
        self
    }

    #[inline]
    pub(crate) fn start(mut self, start: usize) -> Self {
        self.start = start;
        self
    }

    #[inline]
    pub(crate) fn len(mut self, len: usize) -> Self {
        self.len = len;
        self
    }

    #[inline]
    pub(crate) fn in_separator(mut self, in_separator: bool) -> Self {
        self.in_separator = in_separator;
        self
    }

    #[inline]
    pub(crate) fn returns(mut self, returns: Vec<&'a Node<'a>>) -> Self {
        self.returns = returns;
        self
    }

    #[inline]
    pub(crate) fn callbacks(mut self, callbacks: Vec<ContextualizedNode<'a>>) -> Self {
        self.callbacks = callbacks;
        self
    }

    #[inline]
    pub(crate) fn targets(mut self, targets: Vec<ContextualizedNode<'a>>) -> Self {
        self.targets = targets;
        self
    }

    #[inline]
    #[must_use]
    pub(crate) fn build(self) -> Walker<'a> {
        Walker {
            node: self.node,
            status: self.status,

            start: self.start,
            len: self.len,

            in_separator: self.in_separator,

            returns: self.returns,
            callbacks: self.callbacks,
            targets: self.targets,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Status, WalkerBuilder};
    use crate::node::Node;
    use alloc::{vec, vec::Vec};
    use by_address::ByAddress;
    use claim::{assert_err, assert_matches, assert_ok};
    use core::{
        ops::{Bound, RangeBounds},
        ptr,
    };
    use hashbrown::HashSet;

    #[test]
    fn range_bounds_status_none() {
        let node = Node::new();
        let walker = WalkerBuilder::new(&node).start(2).build();

        assert_eq!(walker.start_bound(), Bound::Included(&2));
        assert_eq!(walker.end_bound(), Bound::Excluded(&2));
    }

    #[test]
    fn range_bounds_status_match() {
        let node = Node::new();
        let walker = WalkerBuilder::new(&node)
            .status(Status::Match(2, "foo"))
            .build();

        assert_eq!(walker.start_bound(), Bound::Included(&0));
        assert_eq!(walker.end_bound(), Bound::Excluded(&2));
    }

    #[test]
    fn range_bounds_status_exception() {
        let node = Node::new();
        let walker = WalkerBuilder::new(&node)
            .status(Status::Exception(2, "foo"))
            .build();

        assert_eq!(walker.start_bound(), Bound::Included(&0));
        assert_eq!(walker.end_bound(), Bound::Included(&2));
    }

    #[test]
    fn branch_to_aliases_no_aliases() {
        let node = Node::new();
        let walker = WalkerBuilder::new(&node).build();

        assert_eq!(walker.branch_to_aliases(&mut HashSet::new()).count(), 0);
    }

    #[test]
    fn branch_to_aliases() {
        let alias_node = Node::new();
        let return_node = Node::new();
        let mut node = Node::new();
        node.aliases.push((&alias_node, &return_node));
        let walker = WalkerBuilder::new(&node).build();

        let branches = walker
            .branch_to_aliases(&mut HashSet::new())
            .collect::<Vec<_>>();
        assert_eq!(branches.len(), 1);
        assert!(ptr::eq(branches[0].node, &alias_node));
        assert_eq!(branches[0].returns.len(), 1);
        assert!(ptr::eq(branches[0].returns[0], &return_node));
    }

    #[test]
    fn branch_to_aliases_already_visited() {
        let alias_node = Node::new();
        let return_node = Node::new();
        let mut node = Node::new();
        node.aliases.push((&alias_node, &return_node));
        let walker = WalkerBuilder::new(&node).build();

        let mut visited = HashSet::new();
        visited.insert(ByAddress(&alias_node));
        assert_eq!(walker.branch_to_aliases(&mut visited).count(), 0);
    }

    #[test]
    fn branch_to_aliases_chained() {
        let chained_alias_node = Node::new();
        let chained_return_node = Node::new();
        let mut alias_node = Node::new();
        alias_node
            .aliases
            .push((&chained_alias_node, &chained_return_node));
        let return_node = Node::new();
        let mut node = Node::new();
        node.aliases.push((&alias_node, &return_node));
        let walker = WalkerBuilder::new(&node).build();

        let branches = walker
            .branch_to_aliases(&mut HashSet::new())
            .collect::<Vec<_>>();
        assert_eq!(branches.len(), 2);
        assert!(ptr::eq(branches[0].node, &chained_alias_node));
        assert_eq!(branches[0].returns.len(), 2);
        assert!(ptr::eq(branches[0].returns[0], &return_node));
        assert!(ptr::eq(branches[0].returns[1], &chained_return_node));
        assert!(ptr::eq(branches[1].node, &alias_node));
        assert_eq!(branches[1].returns.len(), 1);
        assert!(ptr::eq(branches[1].returns[0], &return_node));
    }

    #[test]
    fn branch_to_aliases_chained_already_visited() {
        let mut chained_alias_node = Node::new();
        let chained_return_node = Node::new();
        let mut alias_node = Node::new();
        alias_node.aliases.push((
            unsafe {
                // Just evading lifetimes to allow these Nodes to reference each other, don't mind
                // me... (this same thing happens in the actual WordFilter code, but in a much safer
                // fashion with Pins to guarantee validity of the references).
                (&chained_alias_node as *const Node as *const u8 as *const Node)
                    .as_ref()
                    .unwrap()
            },
            &chained_return_node,
        ));
        let return_node = Node::new();
        chained_alias_node.aliases.push((
            unsafe {
                (&alias_node as *const Node as *const u8 as *const Node)
                    .as_ref()
                    .unwrap()
            },
            unsafe {
                (&return_node as *const Node as *const u8 as *const Node)
                    .as_ref()
                    .unwrap()
            },
        ));
        let mut node = Node::new();
        node.aliases.push((&alias_node, &return_node));
        let walker = WalkerBuilder::new(&node).build();

        let branches = walker
            .branch_to_aliases(&mut HashSet::new())
            .collect::<Vec<_>>();
        assert_eq!(branches.len(), 2);
        assert!(ptr::eq(branches[0].node, &chained_alias_node));
        assert_eq!(branches[0].returns.len(), 2);
        assert!(ptr::eq(branches[0].returns[0], &return_node));
        assert!(ptr::eq(branches[0].returns[1], &chained_return_node));
        assert!(ptr::eq(branches[1].node, &alias_node));
        assert_eq!(branches[1].returns.len(), 1);
        assert!(ptr::eq(branches[1].returns[0], &return_node));
    }

    #[test]
    fn step() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut walker = WalkerBuilder::new(&node).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert_err!(walker.step('o'));
    }

    #[test]
    fn step_match() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut walker = WalkerBuilder::new(&node).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert_matches!(walker.status, Status::Match(3, "foo"));
    }

    #[test]
    fn step_exception() {
        let mut node = Node::new();
        node.add_exception("foo");

        let mut walker = WalkerBuilder::new(&node).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert_matches!(walker.status, Status::Exception(3, "foo"));
    }

    #[test]
    fn step_return() {
        let mut node = Node::new();
        node.add_return("foo");
        let return_node = Node::new();

        let mut walker = WalkerBuilder::new(&node).returns(vec![&return_node]).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert!(ptr::eq(walker.node, &return_node));
    }

    #[test]
    fn step_no_return_node() {
        let mut node = Node::new();
        node.add_return("foo");

        let mut walker = WalkerBuilder::new(&node).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_err!(walker.step('o'));
    }

    #[test]
    fn step_return_to_match() {
        let mut node = Node::new();
        node.add_return("foo");
        let mut return_node = Node::new();
        return_node.add_match("");

        let mut walker = WalkerBuilder::new(&node).returns(vec![&return_node]).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert!(ptr::eq(walker.node, &return_node));
        assert_matches!(walker.status, Status::Match(3, ""));
    }

    #[test]
    fn step_return_to_exception() {
        let mut node = Node::new();
        node.add_return("foo");
        let mut return_node = Node::new();
        return_node.add_exception("");

        let mut walker = WalkerBuilder::new(&node).returns(vec![&return_node]).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert!(ptr::eq(walker.node, &return_node));
        assert_matches!(walker.status, Status::Exception(3, ""));
    }

    #[test]
    fn step_return_to_match_in_separator() {
        let mut node = Node::new();
        node.add_return("foo");
        let mut return_node = Node::new();
        return_node.add_match("");

        let mut walker = WalkerBuilder::new(&node).in_separator(true).returns(vec![&return_node]).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert!(ptr::eq(walker.node, &return_node));
        assert!(!walker.in_separator);
        assert_matches!(walker.status, Status::None);
    }

    #[test]
    fn step_return_to_exception_in_separator() {
        let mut node = Node::new();
        node.add_return("foo");
        let mut return_node = Node::new();
        return_node.add_exception("");

        let mut walker = WalkerBuilder::new(&node).in_separator(true).returns(vec![&return_node]).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert!(ptr::eq(walker.node, &return_node));
        assert!(!walker.in_separator);
        assert_matches!(walker.status, Status::None);
    }

    #[test]
    fn step_return_twice() {
        let mut node = Node::new();
        node.add_return("foo");
        let mut return_node_a = Node::new();
        return_node_a.add_return("");
        let return_node_b = Node::new();

        let mut walker = WalkerBuilder::new(&node).returns(vec![&return_node_b, &return_node_a]).build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert!(ptr::eq(walker.node, &return_node_b));
    }
}
