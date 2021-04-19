use crate::node::{self, Node};
use alloc::vec::{self, Vec};
use by_address::ByAddress;
use core::{
    ops::{Bound, RangeBounds},
    ptr,
};
use hashbrown::HashSet;

/// The current status of the `Walker`.
///
/// This indicates whether the `Walker` has reached a `Match` or an `Exception` node.
#[derive(Clone)]
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
    use core::ops::{Bound, RangeBounds};

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
}
