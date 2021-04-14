//! A Word Filter for filtering text.
//!
//! A Word Filter is a system for identifying and censoring specific words or phrases in strings. Common
//! usage includes censoring vulgar or profane language and preventing spam or vandelism in
//! user-provided content.
//!
//! The Word Filter implementation provided here allows for advanced filtering functionality, including:
//! - Finding and censoring filtered words.
//! - Ignoring words that are considered "exceptions".
//! - Allowing specification of "aliases", i.e. strings that can replace other strings (for example, an
//! alias could be created to replace the letter "a" with the character "@").
//! - Ignoring specified separators (such as spaces or other characters) between letters of filtered
//! words.
//!
//! # Usage
//! A [`WordFilter`] can be created using a [`WordFilterBuilder`] as follows:
//!
//! ```
//! use word_filter::WordFilterBuilder;
//!
//! let filter = WordFilterBuilder::new()
//!     .words(&["foo"])
//!     .exceptions(&["foobar"])
//!     .separators(&[" ", "_"])
//!     .aliases(&[("f", "F")])
//!     .build();
//!
//! // The word filter will both identify and censor the word "foo".
//! assert_eq!(filter.censor("Should censor foo"), "Should censor ***");
//!
//! // The word filter does not identify or censor the exception "foobar".
//! assert_eq!(filter.censor("Should not censor foobar"), "Should not censor foobar");
//!
//! // The word filter will ignore separators while matching.
//! assert_eq!(filter.censor("Should censor f o_o"), "Should censor *****");
//!
//! // The word filter checks for aliases while matching.
//! assert_eq!(filter.censor("Should censor Foo"), "Should censor ***");
//! ```

#![warn(
    anonymous_parameters,
    explicit_outlives_requirements,
    missing_docs,
    nonstandard_style,
    rust_2018_idioms,
    single_use_lifetimes,
    unreachable_pub,
    unused_crate_dependencies,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications,
    variant_size_differences
)]
#![warn(
    clippy::nursery,
    clippy::pedantic,
    clippy::restriction::str_to_string,
    clippy::restriction::string_to_string
)]
// This lint is directly contradictory to `unreachable_pub`.
#![allow(clippy::redundant_pub_crate)]
#![no_std]

extern crate alloc;

mod node;
mod utils;
mod walker;

pub mod censor;

use alloc::{borrow::ToOwned, boxed::Box, collections::VecDeque, string::String, vec, vec::Vec};
use by_address::ByAddress;
use censor::replace_chars_with;
use core::{
    iter::FromIterator,
    ops::{Bound, RangeBounds},
    pin::Pin,
};
use hashbrown::{HashMap, HashSet};
use nested_containment_list::NestedContainmentList;
use node::Node;
use str_overlap::Overlap;
use utils::debug_unreachable;
use walker::Walker;

/// The strategy a `WordFilter` should use to match repeated characters.
#[derive(Clone, Copy, Debug)]
pub enum RepeatedCharacterMatchMode {
    /// Allows repeated characters within filtered words.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{RepeatedCharacterMatchMode, WordFilterBuilder};
    ///
    /// let filter = WordFilterBuilder::new()
    ///     .words(&["bar"])
    ///     .repeated_character_match_mode(RepeatedCharacterMatchMode::AllowRepeatedCharacters)
    ///     .build();
    ///
    /// assert!(filter.check("baaar"));
    /// ```
    AllowRepeatedCharacters,
    /// Disallows repeated characters within filtered words.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{RepeatedCharacterMatchMode, WordFilterBuilder};
    ///
    /// let filter = WordFilterBuilder::new()
    ///     .words(&["bar"])
    ///     .repeated_character_match_mode(RepeatedCharacterMatchMode::DisallowRepeatedCharacters)
    ///     .build();
    ///
    /// assert!(!filter.check("baaar"));
    /// ```
    DisallowRepeatedCharacters,
}

impl Default for RepeatedCharacterMatchMode {
    /// Returns the default mode, which is `AllowRepeatedCharacters`.
    fn default() -> Self {
        RepeatedCharacterMatchMode::AllowRepeatedCharacters
    }
}

/// A word filter for identifying filtered words within strings.
///
/// A `WordFilter` is constructed by passing **filtered words**, **exceptions**, **separators**,
/// **aliases**, and **options**. Each of those parameters are defined as follows:
///
/// - **filtered words** - strings that should be identified and censored by the `WordFilter`.
/// - **exceptions** - strings that should explicitly not be identified and censored by the
/// `WordFilter`. Any string that contains filtered word that is contained entirely inside an
/// exception will be ignored.
/// - **separators** - strings that may appear between characters in filtered words and exceptions.
/// - **aliases** - tuples defining alias strings that may replace source strings during matching.
/// These are of the form `(<source string>, <alias string>)`.
/// - **options** - options for the `WordFilter`. See the `Options` struct for more information.
///
/// Example usage:
///
/// ```
/// use word_filter::{censor, RepeatedCharacterMatchMode, WordFilterBuilder};
///
/// let filter = WordFilterBuilder::new()
///     .words(&["foo"])
///     .exceptions(&["foobar"])
///     .separators(&[" ", "_"])
///     .aliases(&[("f", "F")])
///     .repeated_character_match_mode(RepeatedCharacterMatchMode::DisallowRepeatedCharacters)
///     .censor(censor::replace_chars_with!("#"))
///     .build();
/// ```
pub struct WordFilter<'a> {
    root: Node<'a>,
    separator_root: Node<'a>,
    _alias_map: HashMap<String, Pin<Box<Node<'a>>>>,
    repeated_character_match_mode: RepeatedCharacterMatchMode,
    censor: fn(&str) -> String,
}

impl<'a> WordFilter<'a> {
    /// Create new `Walker`s for the aliases at the `walker`'s `current_node`.
    fn push_aliases(
        &self,
        walker: &Walker<'a>,
        new_walkers: &mut Vec<Walker<'a>>,
        visited: &mut HashSet<ByAddress<&Node<'a>>>,
    ) {
        for (alias_node, return_node) in &walker.current_node.aliases {
            if visited.contains(&ByAddress(alias_node)) {
                continue;
            }
            let mut return_nodes = walker.return_nodes.clone();
            return_nodes.push(return_node);
            let alias_walker =
                Walker::new(alias_node, return_nodes, walker.start, walker.len, false);
            visited.insert(ByAddress(alias_node));
            self.push_aliases(&alias_walker, new_walkers, visited);
            visited.remove(&ByAddress(alias_node));
            new_walkers.push(alias_walker);
        }
    }

    /// Finds all `Walker`s that encounter matches.
    ///
    /// This also excludes all `Walker`s that encountered matches but whose ranges also are
    /// contained within ranges are `Walker`s who encountered exceptions.
    fn find_walkers(&self, input: &str) -> impl Iterator<Item = Walker<'_>> {
        let root_walker = Walker::new(&self.root, Vec::new(), 0, 0, false);
        let mut walkers = Vec::new();
        self.push_aliases(&root_walker, &mut walkers, &mut HashSet::new());
        walkers.push(root_walker);
        let mut found = Vec::new();
        for (i, c) in input.chars().enumerate() {
            let mut new_walkers = Vec::new();
            for mut walker in walkers.drain(..) {
                let mut last_walker = walker.clone();
                if walker.step(c) {
                    // Aliases.
                    self.push_aliases(&walker, &mut new_walkers, &mut HashSet::new());
                    // Separators.
                    let mut return_nodes = walker.return_nodes.clone();
                    return_nodes.push(walker.current_node);
                    new_walkers.push(Walker::new(
                        &self.separator_root,
                        return_nodes,
                        walker.start,
                        walker.len,
                        true,
                    ));

                    // Direct path.
                    new_walkers.push(walker);

                    // Repeated characters.
                    if let RepeatedCharacterMatchMode::AllowRepeatedCharacters =
                        self.repeated_character_match_mode
                    {
                        last_walker.len += 1;

                        // Separators.
                        let mut return_nodes = last_walker.return_nodes.clone();
                        return_nodes.push(last_walker.current_node);
                        let mut separator_walker = Walker::new(
                            &self.separator_root,
                            return_nodes,
                            last_walker.start,
                            last_walker.len,
                            true,
                        );
                        separator_walker.repeated_character = Some(c);
                        new_walkers.push(separator_walker);

                        last_walker.repeated_character = Some(c);
                        new_walkers.push(last_walker);
                    }
                } else if let walker::Status::Match(_) = walker.status {
                    found.push(walker);
                } else if let walker::Status::Exception(_) = walker.status {
                    found.push(walker);
                }
            }

            // Add root again.
            new_walkers.push(Walker::new(&self.root, Vec::new(), i + 1, 0, false));
            new_walkers.extend(self.root.aliases.iter().map(|(alias_node, return_node)| {
                Walker::new(alias_node, vec![return_node], i + 1, 0, false)
            }));

            walkers = new_walkers;
        }

        // Evaluate all remaining walkers.
        for walker in walkers.drain(..) {
            match walker.status {
                walker::Status::Match(_) | walker::Status::Exception(_) => found.push(walker),
                walker::Status::None => {}
            }
        }

        // extern crate std;
        // use std::dbg;
        // dbg!(&found.iter().filter_map(|element| if let walker::Status::Match(s) = element.status {
        //     Some((s, element.start_bound(), element.end_bound()))
        // } else {
        //     None
        // }).collect::<Vec<_>>());

        // dbg!(NestedContainmentList::from_iter(found.clone()).into_iter().filter_map(|element| 
        //     if let walker::Status::Match(s) = element.value.status {
        //         Some((s, element.value.start, element.value.len))
        //     } else {
        //         None
        //     }).collect::<Vec<_>>());

        // dbg!(NestedContainmentList::from_iter(found.clone()).into_iter().next().unwrap().sublist().filter_map(|element| 
        //     if let walker::Status::Match(s) = element.value.status {
        //         Some((s, element.value.start, element.value.len))
        //     } else {
        //         None
        //     }).collect::<Vec<_>>());

        // Only return outer-most matched words which aren't part of a longer exception.
        NestedContainmentList::from_iter(found)
            .into_iter()
            .filter_map(|element| {
                let p = element.value;
                if let walker::Status::Match(_) = p.status {
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
    pub fn find(&self, input: &str) -> Box<[&str]> {
        self.find_walkers(input)
            .map(|walker| {
                if let walker::Status::Match(s) = walker.status {
                    s
                } else {
                    unsafe {
                        // SAFETY: All `Walker`s returned from ``find_walkers()` are guaranteed to
                        // be matches. In the event that this changes in the future, this call will
                        // panic when `debug_assertions` is on.
                        debug_unreachable()
                    }
                }
            })
            .collect::<Vec<&str>>()
            .into_boxed_slice()
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
    #[must_use]
    pub fn censor(&self, input: &str) -> String {
        let mut output = String::with_capacity(input.len());
        let mut input_char_indices = input.char_indices();
        // Walkers are sorted on both start and end, due to use of NestedContainmentList.
        let mut prev_end = 0;
        for walker in self.find_walkers(input) {
            // Insert un-censored characters.
            if walker.start > prev_end {
                for _ in 0..(walker.start - prev_end) {
                    output.push(match input_char_indices.next().map(|(_i, c)| c) {
                        Some(c) => c,
                        None => unsafe {
                            // SAFETY: Each `walker` within `walkers` is guaranteed to be within
                            // the bounds of `input`. Additionally, since the `walker`s are ordered
                            // by the ordering provided by the `NestedContainmentList` and are
                            // guaranteed by that same data structure to not include any nested
                            // `walker`s, each subsequent `walker` will cover a new set of `input`
                            // characters. Thus, `input_char_indices.next()` will always return a
                            // value, and the `None` branch will never be reached.
                            debug_unreachable()
                        },
                    })
                }
            }
            // Censor the covered characters for this walker.
            let len = match walker.end_bound() {
                Bound::Included(end) => end + 1,
                _ => unsafe {
                    // SAFETY: The `RangeBounds` on a `Walker` will always be `Bound::Included`, so
                    // we will never reach any other branch.
                    debug_unreachable()
                },
            } - core::cmp::max(walker.start, prev_end);

            let (substring_start, current_char) = match input_char_indices.next() {
                Some((start, c)) => (start, c),
                None => unsafe { debug_unreachable() },
            };
            let substring_end = if len > 1 {
                match input_char_indices.nth(len - 2) {
                    Some((end, c)) => end + c.len_utf8(),
                    None => unsafe { debug_unreachable() },
                }
            } else {
                substring_start + current_char.len_utf8()
            };

            output.push_str(&(self.censor)(&input[substring_start..substring_end]));

            prev_end = match walker.end_bound() {
                Bound::Included(end) => end + 1,
                _ => unsafe {
                    // SAFETY: The `RangeBounds` on a `Walker` will always be `Bound::Included`, so
                    // we will never reach any other branch.
                    debug_unreachable()
                },
            };
        }

        // Add the rest of the characters.
        output.push_str(unsafe {
            // SAFETY: Since the index is obtained from a `CharIndices` `Iterator` over `input`, the
            // index used here will always be on character bounds of `input`, and will never be
            // outside the bounds. Therefore, this usage of `get_unchecked()` is sound.
            input.get_unchecked(
                input_char_indices
                    .next()
                    .map_or_else(|| input.len(), |(i, _c)| i)..,
            )
        });

        output
    }
}

/// A non-consuming builder for a [`WordFilter`].
///
/// Allows configuration of any of the following elements that make up a `WordFilter`, through the
/// corresponding methods:
///
/// - **[`words`]** - Words to be filtered.
/// - **[`exceptions`]** - Words that are not to be filtered.
/// - **[`separators`]** - Values that may appear between characters of words or exceptions.
/// - **[`aliases`]** - Pairs of alias strings and source strings. Alias strings may replace source
/// strings in words and exceptions.
/// - **[`repeated_character_match_mode`]** - The [`RepeatedCharacterMatchMode`] to be used. By default
/// this is set to `RepeatedCharacterMatchMode::AllowRepeatedCharacters`.
/// - **[`censor`]** - The censor to be used. By default this is set to
/// [`censor::replace_chars_with!("*")`].
///
/// These methods can be chained on each other, allowing construction to be performed in a single
/// statement if desired.
///
/// # Example
/// Fully configuring and constructing a `WordFilter` using the `WordFilterBuilder` can be done as
/// follows:
///
/// ```
/// use word_filter::{censor, RepeatedCharacterMatchMode, WordFilterBuilder};
///
/// let filter = WordFilterBuilder::new()
///     .words(&["foo"])
///     .exceptions(&["foobar"])
///     .separators(&[" ", "_"])
///     .aliases(&[("f", "F")])
///     .repeated_character_match_mode(RepeatedCharacterMatchMode::DisallowRepeatedCharacters)
///     .censor(censor::replace_chars_with!("#"))
///     .build();
/// ```
///
/// [`words`]: Self::words
/// [`exceptions`]: Self::exceptions
/// [`separators`]: Self::separators
/// [`aliases`]: Self::aliases
/// [`repeated_character_match_mode`]: Self::repeated_character_match_mode
/// [`censor`]: Self::censor
/// [`censor::replace_chars_with!("*")`]: censor/macro.replace_chars_with.html
#[derive(Clone)]
pub struct WordFilterBuilder<'a> {
    words: Vec<&'a str>,
    exceptions: Vec<&'a str>,
    separators: Vec<&'a str>,
    aliases: Vec<(&'a str, &'a str)>,
    repeated_character_match_mode: RepeatedCharacterMatchMode,
    censor: fn(&str) -> String,
}

impl<'a> WordFilterBuilder<'a> {
    /// Constructs a new `WordFilterBuilder`.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let builder = WordFilterBuilder::new();
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self {
            words: Vec::new(),
            exceptions: Vec::new(),
            separators: Vec::new(),
            aliases: Vec::new(),
            repeated_character_match_mode: RepeatedCharacterMatchMode::AllowRepeatedCharacters,
            censor: replace_chars_with!("*"),
        }
    }

    /// Adds words to be used in building the [`WordFilter`].
    ///
    /// Note that this does not replace any words that have been added prior. Multiple calls to this
    /// method will result in all words being used.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().words(&["foo"]).build();
    /// ```
    #[inline]
    pub fn words(&mut self, words: &[&'a str]) -> &mut Self {
        self.words.extend_from_slice(words);
        self
    }

    /// Adds exceptions to be used in building the [`WordFilter`].
    ///
    /// Note that this does not replace any exceptions that have been added prior. Multiple calls to
    /// this method will result in all exceptions being used.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().exceptions(&["foo"]).build();
    /// ```
    #[inline]
    pub fn exceptions(&mut self, exceptions: &[&'a str]) -> &mut Self {
        self.exceptions.extend_from_slice(exceptions);
        self
    }

    /// Adds separators to be used in building the [`WordFilter`].
    ///
    /// Note that this does not replace any separators that have been added prior. Multiple calls to
    /// this method will result in all separators being used.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().separators(&["_"]).build();
    /// ```
    #[inline]
    pub fn separators(&mut self, separators: &[&'a str]) -> &mut Self {
        self.separators.extend_from_slice(separators);
        self
    }

    /// Adds aliases to be used in building the [`WordFilter`].
    ///
    /// Aliases are tuples defining alias strings that may replace source strings during matching.
    /// These are of the form `(<source string>, <alias string>)`.
    ///
    /// Note that this does not replace any aliases that have been added prior. Multiple calls to
    /// this method will result in all aliases being used.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().aliases(&[("a", "@")]).build();
    /// ```
    #[inline]
    pub fn aliases(&mut self, aliases: &[(&'a str, &'a str)]) -> &mut Self {
        self.aliases.extend_from_slice(aliases);
        self
    }

    /// Sets the [`RepeatedCharacterMatchMode`] to be used by the [`WordFilter`].
    ///
    /// If this is not provided, it will default to
    /// `RepeatedCharacterMatchMode::AllowRepeatedCharacters`.
    ///
    /// # Example
    /// ```
    /// use word_filter::{RepeatedCharacterMatchMode, WordFilterBuilder};
    ///
    /// let filter = WordFilterBuilder::new()
    ///     .repeated_character_match_mode(RepeatedCharacterMatchMode::DisallowRepeatedCharacters)
    ///     .build();
    /// ```
    #[inline]
    pub fn repeated_character_match_mode(&mut self, mode: RepeatedCharacterMatchMode) -> &mut Self {
        self.repeated_character_match_mode = mode;
        self
    }

    /// Sets the censor to be used by the [`WordFilter`].
    ///
    /// A censor is a function mapping from the word to be censored to the censored result. The
    /// default censor is [`censor::replace_chars_with!("*")`].
    ///
    /// # Example
    /// ```
    /// use word_filter::{censor, WordFilterBuilder};
    ///
    /// let filter = WordFilterBuilder::new().censor(censor::replace_chars_with!("#")).build();
    /// ```
    ///
    /// [`censor::replace_chars_with!("*")`]: censor/macro.replace_chars_with.html
    #[inline]
    pub fn censor(&mut self, censor: fn(&str) -> String) -> &mut Self {
        self.censor = censor;
        self
    }

    /// Builds a [`WordFilter`] using the configurations set on the `WordFilterBuilder`.
    ///
    /// Note that this is a non-consuming function, and the `WordFilterBuilder` can therefore be
    /// used after a `WordFilter` is built.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().words(&["foo"]).build();
    /// ```
    #[must_use]
    pub fn build(&self) -> WordFilter<'a> {
        let mut root = Node::new();

        for word in &self.words {
            root.add_match(word);
        }

        for exception in &self.exceptions {
            root.add_exception(exception);
        }

        let mut separator_root = Node::new();
        for separator in &self.separators {
            separator_root.add_return(separator);
        }

        let mut alias_map = HashMap::new();
        for (value, alias) in &self.aliases {
            unsafe {
                alias_map
                    .entry((*value).to_owned())
                    .or_insert_with(|| Box::pin(Node::new()))
                    .as_mut()
                    // SAFETY: Adding an alias to a `Node` will not move the `Node`. Therefore, this
                    // mutation of the `Node` will uphold pin invariants.
                    .get_unchecked_mut()
                    .add_return(alias);
            }
        }
        // Find merged aliases.
        // First, find all aliases that can possibly be combined by a value.
        let mut queue = VecDeque::new();
        for (value, alias) in &self.aliases {
            for (merge_value, _) in &self.aliases {
                let overlap_value = alias.overlap_end(merge_value);
                if overlap_value.is_empty() || overlap_value == *merge_value {
                    continue;
                }
                queue.push_back((
                    (*value).to_owned(),
                    unsafe {
                        // SAFETY: `overlap_value` will always be the prefix of `merge_value`.
                        // Therefore, this will never be out of bounds and it will always uphold
                        // `str` invariants.
                        merge_value.get_unchecked(overlap_value.len()..).to_owned()
                    },
                    (*alias).to_owned(),
                ));
            }
        }
        // Now, find aliases that complete the combination.
        let mut new_aliases = Vec::new();
        while let Some((value, target_value, alias)) = queue.pop_front() {
            for (new_value, new_alias) in &self.aliases {
                if target_value == *new_alias || new_alias.starts_with(&target_value) {
                    new_aliases.push((value.clone() + new_value, alias.clone() + new_alias));
                } else if target_value.starts_with(new_alias) {
                    // If the combination isn't complete, push it to the queue and try again.
                    queue.push_back((
                        value.clone() + new_value,
                        unsafe {
                            // SAFETY: Since `new_alias` is the prefix of `target_value`, this will
                            // never be out of bounds and will always uphold `str` invariants.
                            target_value.get_unchecked(new_alias.len()..).to_owned()
                        },
                        alias.clone() + new_alias,
                    ));
                }
            }
        }
        for (value, alias) in new_aliases {
            unsafe {
                alias_map
                    .entry(value)
                    .or_insert_with(|| Box::pin(Node::new()))
                    .as_mut()
                    // SAFETY: Adding a return to a `Node` will not move the `Node`. Therefore, this
                    // mutation of the `Node` will uphold pin invariants.
                    .get_unchecked_mut()
                    .add_return(&alias);
            }
        }

        // Apply aliases on each other.
        let keys = alias_map.keys().cloned().collect::<Vec<_>>();
        for value in &keys {
            for alias_value in &keys {
                if value == alias_value {
                    continue;
                }
                let alias_node = unsafe {
                    // SAFETY: The obtained reference to a Node is self-referential within the
                    // WordFilter struct. The only reason this conversion from reference to pointer
                    // and back again is necessary is to make the reference lifetime-agnostic to
                    // allow the self-reference. This is safe, because every Node owned in the graph
                    // by the WordFilter is pinned in place in memory, meaning it will only ever
                    // move when the WordFilter is dropped. Therefore, this reference will be valid
                    // for as long as it is used by the WordFilter.
                    &*(&*alias_map[alias_value] as *const Node<'_>)
                };
                unsafe {
                    match alias_map.get_mut(value) {
                        Some(node) => node,
                        None => {
                            // SAFETY: We know that `value` is a valid key in `alias_map`, and
                            // therefore `get_mut()` will always return a value.
                            debug_unreachable()
                        }
                    }
                    .as_mut()
                    // SAFETY: Adding an alias to a `Node` will not move the `Node`. Therefore,
                    // this mutation of the `Node` will uphold pin invariants.
                    .get_unchecked_mut()
                    .add_alias(alias_value, alias_node);
                }
            }
        }
        for (value, node) in &alias_map {
            unsafe {
                // SAFETY: The obtained reference to a Node is self-referential within the
                // WordFilter struct. The only reason this conversion from reference to pointer and
                // back again is necessary is to make the reference lifetime-agnostic to allow the
                // self-reference. This is safe, because every Node owned in the graph by the
                // WordFilter is pinned in place in memory, meaning it will only ever move when the
                // WordFilter is dropped. Therefore, this reference will be valid for as long as it
                // is used by the WordFilter.
                root.add_alias(value, &*(&**node as *const Node<'_>));
            }
        }

        WordFilter {
            root,
            separator_root,
            _alias_map: alias_map,
            repeated_character_match_mode: self.repeated_character_match_mode,
            censor: self.censor,
        }
    }
}

impl Default for WordFilterBuilder<'_> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::{replace_chars_with, RepeatedCharacterMatchMode, WordFilterBuilder};
    use alloc::{vec, vec::Vec};

    #[test]
    fn find() {
        let filter = WordFilterBuilder::new().words(&["foo"]).build();

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn check() {
        let filter = WordFilterBuilder::new().words(&["foo"]).build();

        assert!(filter.check("foo"));
        assert!(!filter.check("bar"));
    }

    #[test]
    fn check_only_partial() {
        let filter = WordFilterBuilder::new().words(&["foo"]).build();

        assert!(!filter.check("fo"));
    }

    #[test]
    fn censor() {
        let filter = WordFilterBuilder::new().words(&["foo"]).build();

        assert_eq!(filter.censor("foo"), "***");
    }

    #[test]
    fn exceptions() {
        let filter = WordFilterBuilder::new()
            .words(&["foo"])
            .exceptions(&["afoo", "foob", "cfood"])
            .build();

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("afoo"), Vec::new().into_boxed_slice());
        assert_eq!(filter.find("foob"), Vec::new().into_boxed_slice());
        assert_eq!(filter.find("cfood"), Vec::new().into_boxed_slice());
    }

    #[test]
    fn exceptions_and_matches() {
        let filter = WordFilterBuilder::new()
            .words(&["foo"])
            .exceptions(&["foobar"])
            .build();

        assert_eq!(filter.find("foobarfoo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn separators() {
        let filter = WordFilterBuilder::new()
            .words(&["foo"])
            .separators(&[" "])
            .build();

        assert_eq!(filter.find("f oo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn separator_between_repeated_characters() {
        let filter = WordFilterBuilder::new()
            .words(&["bar"])
            .separators(&[" "])
            .build();

        assert_eq!(filter.find("b a a r"), vec!["bar"].into_boxed_slice());
        assert_eq!(filter.censor(" b a a r "), " ******* ");
    }

    #[test]
    fn aliases() {
        let filter = WordFilterBuilder::new()
            .words(&["foo"])
            .aliases(&[("o", "a")])
            .build();

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fao"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("foa"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("faa"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn aliases_on_aliases() {
        let filter = WordFilterBuilder::new()
            .words(&["foo"])
            .aliases(&[("o", "a"), ("a", "b")])
            .build();

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fbo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fob"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fbb"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn merged_aliases() {
        let filter = WordFilterBuilder::new()
            .words(&["bar"])
            .aliases(&[("b", "cd"), ("a", "ef"), ("de", "g")])
            .build();

        assert_eq!(filter.find("cgfr"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn merged_aliases_contiguous() {
        let filter = WordFilterBuilder::new()
            .words(&["ahj"])
            .aliases(&[("a", "bc"), ("cdef", "g"), ("h", "de"), ("j", "fi")])
            .build();

        assert_eq!(filter.find("bcdefi"), vec!["ahj"].into_boxed_slice());
        assert_eq!(filter.find("bgi"), vec!["ahj"].into_boxed_slice());
    }

    #[test]
    fn merged_aliases_over_full_match() {
        let filter = WordFilterBuilder::new()
            .words(&["bar"])
            .aliases(&[("b", "x"), ("a", "y"), ("r", "z"), ("xyz", "w")])
            .build();

        assert_eq!(filter.find("w"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn recursive_alias_no_overflow() {
        // Make sure recursive aliases don't cause a stack overflow.
        let filter = WordFilterBuilder::new()
            .words(&["bar"])
            .aliases(&[("a", "b"), ("b", "a")])
            .repeated_character_match_mode(RepeatedCharacterMatchMode::DisallowRepeatedCharacters)
            .build();

        assert_eq!(filter.find("abr"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn alias_after_separator() {
        let filter = WordFilterBuilder::new()
            .words(&["bar"])
            .separators(&[" "])
            .aliases(&[("a", "A")])
            .build();

        assert_eq!(filter.find("b Ar"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn repeated_characters_allowed() {
        let filter = WordFilterBuilder::new()
            .words(&["bar"])
            .repeated_character_match_mode(RepeatedCharacterMatchMode::AllowRepeatedCharacters)
            .build();

        assert_eq!(filter.find("bbbaaaarrrr"), vec!["bar"].into_boxed_slice());
        assert_eq!(filter.censor("baaar"), "*****");
    }

    #[test]
    fn repeated_characters_disallowed() {
        let filter = WordFilterBuilder::new()
            .words(&["bar"])
            .repeated_character_match_mode(RepeatedCharacterMatchMode::DisallowRepeatedCharacters)
            .build();

        assert_eq!(filter.find("bbbaaaarrrr"), vec![].into_boxed_slice());
    }

    #[test]
    fn custom_censor() {
        let filter = WordFilterBuilder::new()
            .words(&["foo"])
            .censor(replace_chars_with!("#"))
            .build();

        assert_eq!(filter.censor("foo"), "###");
    }

    #[test]
    fn separator_at_front_and_back_of_match() {
        let filter = WordFilterBuilder::new()
            .words(&["foo"])
            .separators(&[" "])
            .build();

        assert_eq!(filter.censor("bar foo bar"), "bar *** bar");
    }

    #[test]
    fn default_builder() {
        let filter = WordFilterBuilder::default().words(&["foo"]).build();

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn censor_repeating() {
        let filter = WordFilterBuilder::new().words(&["foo", "bar"]).build();

        assert_eq!(filter.censor("fbar"), "f***");
    }
}
