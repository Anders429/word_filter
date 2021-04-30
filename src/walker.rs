//! Walker for [`WordFilter`] internal searching.
//!
//! [`Walker`] provides an efficient way for the `WordFilter` to search its own directional graph
//! for matches to a given string.
//!
//! Use of a `Walker` allows for multiple simultaneous searches to all maintain their own context.
//! This allows for splitting of paths at aliases, searching for separators, and searching at
//! different start locations within the string simultaneously.
//!
//! [`WordFilter`]: crate::WordFilter

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

/// A contextualizing wrapper for a [`Node`].
///
/// Indicates what context the `Node` should be evaluated in.
///
/// [`Node`]: crate::node::Node
#[derive(Clone, Debug)]
pub(crate) enum ContextualizedNode<'a> {
    /// The `Node` should be evaluated in a direct path context.
    InDirectPath(&'a Node<'a>),
    /// The `Node` should be evaluated in a subgraph context.
    InSubgraph(&'a Node<'a>),
}

/// A specialized walker for traveling through the `WordFilter`'s `Node` graph.
///
/// The `Walker` keeps track of the current context within the `Node` (as in, the current walker
/// location, a stack of return nodes, etc.), as well as information about the `Walker`'s location
/// within the original source string passed into the `WordFilter`.
///
/// In order to progress the `Walker` forward, the `step()` method is provided, which allows the
/// user to step the `Walker` through each character in a string.
#[derive(Clone, Debug)]
pub(crate) struct Walker<'a> {
    pub(crate) node: &'a Node<'a>,
    pub(crate) status: Status<'a>,

    pub(crate) start: usize,
    len: usize,

    pub(crate) in_separator: bool,

    pub(crate) returns: Vec<&'a Node<'a>>,
    pub(crate) callbacks: Vec<ContextualizedNode<'a>>,
    pub(crate) targets: Vec<ContextualizedNode<'a>>,
}

impl<'a> Walker<'a> {
    /// Create new `Walker`s pointing to alias paths connected to the current node.
    pub(crate) fn branch_to_aliases(&self) -> vec::IntoIter<Walker<'a>> {
        self.internal_branch_to_aliases(&mut HashSet::new())
    }

    fn internal_branch_to_aliases(
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
            result.extend(alias_walker.internal_branch_to_aliases(visited));
            result.extend(alias_walker.internal_branch_to_grapheme_subgraphs(visited));
            visited.remove(&ByAddress(alias_node));

            result.push(alias_walker);
        }

        result.into_iter()
    }

    /// Create new `Walker`s pointing to grapheme subgraphs connected to the current node.
    pub(crate) fn branch_to_grapheme_subgraphs(&self) -> vec::IntoIter<Walker<'a>> {
        self.internal_branch_to_grapheme_subgraphs(&mut HashSet::new())
    }

    fn internal_branch_to_grapheme_subgraphs(
        &self,
        visited: &mut HashSet<ByAddress<&Node<'a>>>,
    ) -> vec::IntoIter<Walker<'a>> {
        let mut result = Vec::new();

        for (grapheme_subgraph_node, grapheme_return_node) in &self.node.grapheme_subgraphs {
            let mut grapheme_walker = self.clone();
            grapheme_walker.node = grapheme_subgraph_node;
            grapheme_walker.returns.push(grapheme_return_node);
            grapheme_walker.in_separator = false;

            result.extend(grapheme_walker.internal_branch_to_aliases(visited));

            result.push(grapheme_walker);
        }

        result.into_iter()
    }

    /// Processes a return node.
    ///
    /// If the return node returns to another node which is itself a return node, it will be
    /// evaluated recursively.
    ///
    /// If successful, this will return an iterator containing branched `Walker`s from the evaluation.
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
                    callback_walker.callbacks.pop();

                    result.extend(callback_walker.branch_to_aliases().map(
                        |mut walker| {
                            walker
                                .targets
                                .push(ContextualizedNode::InSubgraph(self.node));
                            walker
                                .callbacks
                                .push(ContextualizedNode::InSubgraph(callback_node));
                            walker.returns.push(self.node);
                            walker
                        },
                    ));

                    result.extend(
                        callback_walker
                            .branch_to_grapheme_subgraphs(
                                )
                            .map(|mut walker| {
                                walker
                                    .targets
                                    .push(ContextualizedNode::InSubgraph(self.node));
                                walker
                                    .callbacks
                                    .push(ContextualizedNode::InSubgraph(callback_node));
                                walker.returns.push(self.node);
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
            node::Type::Match(ref word) => {
                if self.in_separator {
                    self.in_separator = false;
                } else {
                    self.status = Status::Match(self.start + self.len + 1, word);
                }
            }
            node::Type::Exception(ref exception) => {
                if self.in_separator {
                    self.in_separator = false;
                } else {
                    self.status = Status::Exception(self.start + self.len + 1, exception);
                }
            }
        }

        Ok(result.into_iter())
    }

    /// Step the `Walker` along the character 'c'.
    ///
    /// If successful, returns an iterator of branched `Walker`s.
    pub(crate) fn step(&mut self, c: char) -> Result<vec::IntoIter<Walker<'a>>, ()> {
        let mut branches = Vec::new();

        match self.node.children.get(&c) {
            Some(node) => {
                if let Some(ContextualizedNode::InDirectPath(target_node)) = self.targets.last() {
                    if !ptr::eq(node.as_ref().get_ref(), *target_node) {
                        return Err(());
                    }
                    self.targets.pop();
                }
                if let Some(ContextualizedNode::InDirectPath(callback_node)) = self.callbacks.last()
                {
                    let mut callback_walker = self.clone();
                    callback_walker.node = callback_node;
                    callback_walker.len += 1;
                    callback_walker.callbacks.pop();

                    branches.extend(callback_walker.branch_to_aliases().map(
                        |mut walker| {
                            walker.targets.push(ContextualizedNode::InSubgraph(node));
                            walker
                                .callbacks
                                .push(ContextualizedNode::InSubgraph(callback_node));
                            walker
                        },
                    ));

                    branches.extend(
                        callback_walker
                            .branch_to_grapheme_subgraphs(
                                )
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
                self.node = node;
                match self.node.node_type {
                    node::Type::Standard => {}
                    node::Type::Return => {
                        branches.extend(self.evaluate_return_node()?);
                    }
                    node::Type::Match(ref word) => {
                        self.status = Status::Match(self.start + self.len + 1, word);
                    }
                    node::Type::Exception(ref exception) => {
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
/// A match will always have an excluded `end_bound()`, while an exception will always have an
/// included `end_bound()`. This ensures that exceptions will always trump matches when `Walker`s
/// are evaluated in a `NestedContainmentList`.
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

#[allow(dead_code)]
impl<'a> WalkerBuilder<'a> {
    #[inline]
    #[must_use]
    pub(crate) fn new(node: &'a Node<'a>) -> Self {
        Self {
            node,
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
    use super::{ContextualizedNode, Status, WalkerBuilder};
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

        assert_eq!(walker.branch_to_aliases().count(), 0);
    }

    #[test]
    fn branch_to_aliases() {
        let alias_node = Node::new();
        let return_node = Node::new();
        let mut node = Node::new();
        node.aliases.push((&alias_node, &return_node));
        let walker = WalkerBuilder::new(&node).build();

        let branches = walker
            .branch_to_aliases()
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
        assert_eq!(walker.internal_branch_to_aliases(&mut visited).count(), 0);
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
            .branch_to_aliases()
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
                (&chained_alias_node as *const Node<'_> as *const u8 as *const Node<'_>)
                    .as_ref()
                    .unwrap()
            },
            &chained_return_node,
        ));
        let return_node = Node::new();
        chained_alias_node.aliases.push((
            unsafe {
                (&alias_node as *const Node<'_> as *const u8 as *const Node<'_>)
                    .as_ref()
                    .unwrap()
            },
            unsafe {
                (&return_node as *const Node<'_> as *const u8 as *const Node<'_>)
                    .as_ref()
                    .unwrap()
            },
        ));
        let mut node = Node::new();
        node.aliases.push((&alias_node, &return_node));
        let walker = WalkerBuilder::new(&node).build();

        let branches = walker
            .branch_to_aliases()
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

        let mut walker = WalkerBuilder::new(&node)
            .returns(vec![&return_node])
            .build();

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

        let mut walker = WalkerBuilder::new(&node)
            .returns(vec![&return_node])
            .build();

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

        let mut walker = WalkerBuilder::new(&node)
            .returns(vec![&return_node])
            .build();

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

        let mut walker = WalkerBuilder::new(&node)
            .in_separator(true)
            .returns(vec![&return_node])
            .build();

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

        let mut walker = WalkerBuilder::new(&node)
            .in_separator(true)
            .returns(vec![&return_node])
            .build();

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

        let mut walker = WalkerBuilder::new(&node)
            .returns(vec![&return_node_b, &return_node_a])
            .build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert!(ptr::eq(walker.node, &return_node_b));
    }

    #[test]
    fn step_callback_in_direct_path() {
        let mut node = Node::new();
        node.add_match("foo");
        let callback_node = Node::new();

        let mut walker = WalkerBuilder::new(&node)
            .callbacks(vec![ContextualizedNode::InDirectPath(&callback_node)])
            .build();

        let branched_walkers = walker.step('f').unwrap().collect::<Vec<_>>();
        assert_eq!(branched_walkers.len(), 1);
        assert!(ptr::eq(branched_walkers[0].node, &callback_node));
        match branched_walkers[0].targets[0] {
            ContextualizedNode::InDirectPath(target_node) => {
                assert!(ptr::eq(target_node, &*node.children[&'f']))
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn step_callback_in_subgraph() {
        let mut node = Node::new();
        node.add_return("foo");
        let return_node = Node::new();
        let callback_node = Node::new();

        let mut walker = WalkerBuilder::new(&node)
            .callbacks(vec![ContextualizedNode::InSubgraph(&callback_node)])
            .returns(vec![&return_node])
            .build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        let branched_walkers = walker.step('o').unwrap().collect::<Vec<_>>();
        assert_eq!(branched_walkers.len(), 1);
        assert!(ptr::eq(branched_walkers[0].node, &callback_node));
        match branched_walkers[0].targets[0] {
            ContextualizedNode::InDirectPath(target_node) => {
                assert!(ptr::eq(target_node, &return_node))
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn step_target_in_direct_path() {
        let mut node = Node::new();
        node.add_match("foo");

        let mut walker = WalkerBuilder::new(&node)
            .targets(vec![ContextualizedNode::InDirectPath(
                &*node.children[&'f'],
            )])
            .build();

        assert_ok!(walker.step('f'));
        assert_eq!(walker.targets.len(), 0);
    }

    #[test]
    fn step_target_in_subgraph() {
        let mut node = Node::new();
        node.add_return("foo");
        let return_node = Node::new();

        let mut walker = WalkerBuilder::new(&node)
            .targets(vec![ContextualizedNode::InSubgraph(&return_node)])
            .returns(vec![&return_node])
            .build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_ok!(walker.step('o'));
        assert_eq!(walker.targets.len(), 0);
    }

    #[test]
    fn step_wrong_target_in_direct_path() {
        let mut node = Node::new();
        node.add_match("foo");
        let target_node = Node::new();

        let mut walker = WalkerBuilder::new(&node)
            .targets(vec![ContextualizedNode::InDirectPath(&target_node)])
            .build();

        assert_err!(walker.step('f'));
    }

    #[test]
    fn step_wrong_target_in_subgraph() {
        let mut node = Node::new();
        node.add_return("foo");
        let return_node = Node::new();
        let target_node = Node::new();

        let mut walker = WalkerBuilder::new(&node)
            .targets(vec![ContextualizedNode::InSubgraph(&target_node)])
            .returns(vec![&return_node])
            .build();

        assert_ok!(walker.step('f'));
        assert_ok!(walker.step('o'));
        assert_err!(walker.step('o'));
    }
}
