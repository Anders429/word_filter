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
use alloc::{vec, vec::Vec};
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
    #[inline]
    pub(crate) fn branch_to_alias_subgraphs(&self) -> vec::IntoIter<Walker<'a>> {
        self.branch_to_alias_subgraphs_internal(&mut HashSet::new())
    }

    /// Create new `Walker`s pointing to grapheme paths connected to the current node.
    #[inline]
    pub(crate) fn branch_to_grapheme_subgraphs(&self) -> vec::IntoIter<Walker<'a>> {
        self.branch_to_grapheme_subgraphs_internal(&mut HashSet::new())
    }

    fn branch_to_alias_subgraphs_internal(
        &self,
        visited: &mut HashSet<ByAddress<&Node<'a>>>,
    ) -> vec::IntoIter<Walker<'a>> {
        let mut result = Vec::new();

        for (alias_node, return_node) in self.node.alias_subgraphs {
            if visited.contains(&ByAddress(alias_node)) {
                continue;
            }
            let mut alias_walker = self.clone();
            alias_walker.node = alias_node;
            alias_walker.returns.push(return_node);
            alias_walker.in_separator = false;

            visited.insert(ByAddress(alias_node));
            result.extend(alias_walker.branch_to_alias_subgraphs_internal(visited));
            result.extend(alias_walker.branch_to_grapheme_subgraphs_internal(visited));
            visited.remove(&ByAddress(alias_node));

            result.push(alias_walker);
        }

        result.into_iter()
    }

    fn branch_to_grapheme_subgraphs_internal(
        &self,
        visited: &mut HashSet<ByAddress<&Node<'a>>>,
    ) -> vec::IntoIter<Walker<'a>> {
        let mut result = Vec::new();

        for (grapheme_subgraph_node, grapheme_return_node) in self.node.grapheme_subgraphs {
            let mut grapheme_walker = self.clone();
            grapheme_walker.node = grapheme_subgraph_node;
            grapheme_walker.returns.push(grapheme_return_node);
            grapheme_walker.in_separator = false;

            result.extend(grapheme_walker.branch_to_alias_subgraphs_internal(visited));

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

        match self.node.r#type {
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

                    result.extend(
                        callback_walker
                            .branch_to_alias_subgraphs()
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

                    result.extend(callback_walker.branch_to_grapheme_subgraphs().map(
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

    /// Step the `Walker` along the character 'c'.
    ///
    /// If successful, returns an iterator of branched `Walker`s.
    pub(crate) fn step(&mut self, c: char) -> Result<vec::IntoIter<Walker<'a>>, ()> {
        let mut branches = Vec::new();

        match self.node.children(c) {
            Some(node) => {
                if let Some(ContextualizedNode::InDirectPath(target_node)) = self.targets.last() {
                    if !ptr::eq(node, *target_node) {
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

                    branches.extend(callback_walker.branch_to_alias_subgraphs().map(
                        |mut walker| {
                            walker.targets.push(ContextualizedNode::InSubgraph(node));
                            walker
                                .callbacks
                                .push(ContextualizedNode::InSubgraph(callback_node));
                            walker
                        },
                    ));

                    branches.extend(callback_walker.branch_to_grapheme_subgraphs().map(
                        |mut walker| {
                            walker.targets.push(ContextualizedNode::InSubgraph(node));
                            walker
                                .callbacks
                                .push(ContextualizedNode::InSubgraph(callback_node));
                            walker
                        },
                    ));

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
                match self.node.r#type {
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
        }
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
