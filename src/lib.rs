#![no_std]

extern crate alloc;

pub mod censor;
pub mod node;

mod walker;

use alloc::{string::String, vec, vec::Vec};
use core::{
    iter::FromIterator,
    ops::{Bound, RangeBounds},
};
use debug_unreachable::debug_unreachable;
use nested_containment_list::NestedContainmentList;
use node::Node;
use walker::{ContextualizedNode, Walker, WalkerBuilder};

#[derive(Debug)]
pub struct WordFilter<'a, const N: usize> {
    pub root: Node<'a>,
    pub separator_root: Node<'a>,
    pub nodes: [Node<'a>; N],
}

impl<const N: usize> WordFilter<'_, N> {
    /// Spawns new `Walker`s at the `WordFilter`'s root position, returning them in an iterator.
    ///
    /// This spawns a `Walker` at root, plus `Walker`s at the root's alias and grapheme subgraphs.
    ///
    /// Each spawned `Walker` will have a start position equal to `start`.
    fn spawn_root_walkers_from_start_position(&self, start: usize) -> vec::IntoIter<Walker<'_>> {
        let mut walkers = Vec::new();

        let mut root_walker_builder = WalkerBuilder::new(&self.root).start(start);
        root_walker_builder =
            root_walker_builder.callbacks(vec![ContextualizedNode::InDirectPath(&self.root)]);
        let root_walker = root_walker_builder.build();
        walkers.extend(
            root_walker
                .branch_to_alias_subgraphs()
                .map(|mut walker| {
                    walker
                        .callbacks
                        .push(ContextualizedNode::InSubgraph(&self.root));
                    walker
                }),
        );
        walkers.extend(
            root_walker
                .branch_to_grapheme_subgraphs()
                .map(|mut walker| {
                    walker
                        .callbacks
                        .push(ContextualizedNode::InSubgraph(&self.root));
                    walker
                }),
        );
        walkers.push(root_walker);

        walkers.into_iter()
    }

    /// Finds all `Walker`s that encounter matches.
    ///
    /// This also excludes all `Walker`s that encountered matches but whose ranges also are
    /// contained within ranges are `Walker`s who encountered exceptions.
    fn find_walkers(&self, input: &str) -> impl Iterator<Item = Walker<'_>> {
        let mut walkers: Vec<Walker<'_>> = self.spawn_root_walkers_from_start_position(0).collect();

        let mut found = Vec::new();
        for (i, c) in input.chars().enumerate() {
            let mut new_walkers = Vec::new();
            for mut walker in walkers.drain(..) {
                match walker.step(c) {
                    Ok(branches) => {
                        // New branches.
                        new_walkers.extend(branches.clone().map(|walker| {
                            let mut separator_walker = walker.clone();
                            separator_walker.node = &self.separator_root;
                            separator_walker.returns.push(walker.node);
                            separator_walker.in_separator = true;
                            separator_walker
                                .callbacks
                                .push(ContextualizedNode::InSubgraph(walker.node));
                            separator_walker
                                .targets
                                .push(ContextualizedNode::InSubgraph(walker.node));
                            separator_walker
                        }));
                        new_walkers.extend(branches);

                        // Aliases.
                        let alias_walkers = walker.branch_to_alias_subgraphs();
                        new_walkers.extend(alias_walkers.map(|mut inner_walker| {
                            inner_walker
                                .callbacks
                                .push(ContextualizedNode::InSubgraph(walker.node));
                            inner_walker
                        }));

                        // Graphemes.
                        let grapheme_walkers =
                            walker.branch_to_grapheme_subgraphs();
                        new_walkers.extend(grapheme_walkers.map(|mut inner_walker| {
                            inner_walker
                                .callbacks
                                .push(ContextualizedNode::InSubgraph(walker.node));
                            inner_walker
                        }));

                        // Separators.
                        let mut separator_walker = walker.clone();
                        separator_walker.node = &self.separator_root;
                        separator_walker.returns.push(walker.node);
                        separator_walker.in_separator = true;
                        separator_walker
                            .callbacks
                            .push(ContextualizedNode::InSubgraph(walker.node));
                        separator_walker
                            .targets
                            .push(ContextualizedNode::InSubgraph(walker.node));
                        new_walkers.push(separator_walker);

                        // Direct path.
                        walker
                            .callbacks
                            .push(ContextualizedNode::InDirectPath(walker.node));
                        new_walkers.push(walker);
                    }
                    Err(_) => match walker.status {
                        walker::Status::Match(_, _) | walker::Status::Exception(_, _) => {
                            found.push(walker)
                        }
                        _ => {}
                    },
                }
            }

            // Add root again.
            new_walkers.extend(self.spawn_root_walkers_from_start_position(i + 1));

            walkers = new_walkers;
        }

        // Evaluate all remaining walkers.
        for walker in walkers.drain(..) {
            match walker.status {
                walker::Status::Match(_, _) | walker::Status::Exception(_, _) => found.push(walker),
                walker::Status::None => {}
            }
        }

        // Only return outer-most matched words which aren't part of a longer exception.
        NestedContainmentList::from_iter(found)
            .into_iter()
            .filter_map(|element| {
                let p = element.value;
                if let walker::Status::Match(_, _) = p.status {
                    Some(p)
                } else {
                    None
                }
            })
    }

    /// Find all filtered words matched by `input`.
    ///
    /// Returns a boxed slice containing all matched filtered words in order of appearance.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().words(&["foo"]).build();
    ///
    /// assert_eq!(filter.find("this string contains foo"), vec!["foo"].into_boxed_slice());
    /// ```
    #[must_use]
    #[allow(clippy::missing_panics_doc)] // debug_unreachable won't ever actually panic.
    pub fn find(&self, input: &str) -> impl Iterator<Item = &str> {
        self.find_walkers(input).map(|walker| {
            if let walker::Status::Match(_, s) = walker.status {
                s
            } else {
                unsafe {
                    // SAFETY: All `Walker`s returned from ``find_walkers()` are guaranteed to
                    // be matches. In the event that this changes in the future, this call will
                    // panic when `debug_assertions` is on.
                    debug_unreachable!()
                }
            }
        })
    }

    /// Check whether `input` contains any filtered words.
    ///
    /// Returns `true` if matches are found, and `false` otherwise.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().words(&["foo"]).build();
    ///
    /// assert!(filter.check("this string contains foo"));
    /// ```
    #[must_use]
    pub fn check(&self, input: &str) -> bool {
        self.find_walkers(input).next().is_some()
    }

    #[must_use]
    #[allow(clippy::missing_panics_doc)] // debug_unreachable won't ever actually panic.
    pub fn censor_with(&self, input: &str, censor: fn(&str) -> String) -> String {
        let mut output = String::with_capacity(input.len());
        let mut char_indices = input.char_indices();
        // Walkers are sorted on both start and end, due to use of NestedContainmentList.
        let mut prev_end = 0;
        for walker in self.find_walkers(input) {
            // Insert un-censored characters.
            if walker.start > prev_end {
                for _ in 0..(walker.start - prev_end) {
                    output.push(match char_indices.next().map(|(_i, c)| c) {
                        Some(c) => c,
                        None => unsafe {
                            // SAFETY: Each `walker` within `walkers` is guaranteed to be within
                            // the bounds of `input`. Additionally, since the `walker`s are ordered
                            // by the ordering provided by the `NestedContainmentList` and are
                            // guaranteed by that same data structure to not include any nested
                            // `walker`s, each subsequent `walker` will cover a new set of `input`
                            // characters. Thus, `input_char_indices.next()` will always return a
                            // value, and the `None` branch will never be reached.
                            debug_unreachable!()
                        },
                    })
                }
            }
            // Censor the covered characters for this walker.
            let len = match walker.end_bound() {
                Bound::Excluded(end) => end + 1,
                _ => continue,
            } - core::cmp::max(walker.start, prev_end);

            let (substring_start, current_char) = match char_indices.next() {
                Some((start, c)) => (start, c),
                None => unsafe { debug_unreachable!() },
            };
            let substring_end = if len > 2 {
                match char_indices.nth(len - 3) {
                    Some((end, c)) => end + c.len_utf8(),
                    None => unsafe { debug_unreachable!() },
                }
            } else {
                substring_start + current_char.len_utf8()
            };

            output.push_str(&(censor)(&input[substring_start..substring_end]));

            prev_end = match walker.end_bound() {
                Bound::Excluded(end) => end + 1,
                _ => unsafe {
                    // SAFETY: The `end_bound` on the `walker` will always be `Bound::Excluded`,
                    // since any other branch resulted in a `continue` above.
                    debug_unreachable!()
                },
            };
        }

        // Add the rest of the characters.
        output.push_str(char_indices.as_str());

        output
    }

    /// Censor all filtered words within `input`.
    ///
    /// Returns a newly-allocated `String` with all filtered words censored using the `CensorMode`
    /// strategy, as defined during building.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// // Note that the WordFilterBuilder uses CensorMode::ReplaceAllWith('*') by default.
    /// let filter = WordFilterBuilder::new().words(&["foo"]).build();
    ///
    /// assert_eq!(filter.censor("this string contains foo"), "this string contains ***");
    /// ```
    #[inline]
    #[must_use]
    pub fn censor(&self, input: &str) -> String {
        self.censor_with(input, censor::replace_graphemes_with!("*"))
    }
}

#[cfg(test)]
mod tests {
    use super::{node, WordFilter};

    static FILTER: WordFilter<0> = WordFilter {
        root: node::Node {
            r#type: node::Type::Standard,
            children: |_| None,
            alias_subgraphs: &[(&FILTER.separator_root, &FILTER.root)],
            grapheme_subgraphs: &[],
        },
        separator_root: node::Node {
            r#type: node::Type::Standard,
            children: |_| None,
            alias_subgraphs: &[],
            grapheme_subgraphs: &[],
        },
        nodes: [],
    };

    #[test]
    fn test() {
        extern crate std;
        std::dbg!(&FILTER);
        assert!(false);
    }
}
