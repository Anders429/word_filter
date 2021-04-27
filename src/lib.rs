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
mod walker;

pub mod censor;

use alloc::{
    borrow::ToOwned,
    boxed::Box,
    collections::VecDeque,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use censor::replace_graphemes_with;
use core::{
    fmt,
    iter::FromIterator,
    marker::PhantomData,
    ops::{Bound, RangeBounds},
    pin::Pin,
};
use debug_unreachable::debug_unreachable;
use hashbrown::{HashMap, HashSet};
use nested_containment_list::NestedContainmentList;
use node::Node;
use str_overlap::Overlap;
use walker::{ContextualizedNode, Walker, WalkerBuilder};

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
///     .censor(censor::replace_graphemes_with!("#"))
///     .build();
/// ```
pub struct WordFilter<'a> {
    root: Node<'a>,
    separator_root: Node<'a>,
    _alias_map: HashMap<String, Pin<Box<Node<'a>>>>,
    repeated_character_match_mode: RepeatedCharacterMatchMode,
    censor: fn(&str) -> String,
}

impl WordFilter<'_> {
    /// Finds all `Walker`s that encounter matches.
    ///
    /// This also excludes all `Walker`s that encountered matches but whose ranges also are
    /// contained within ranges are `Walker`s who encountered exceptions.
    fn find_walkers(&self, input: &str) -> impl Iterator<Item = Walker<'_>> {
        let mut root_walker_builder = WalkerBuilder::new(&self.root);
        if let RepeatedCharacterMatchMode::AllowRepeatedCharacters =
            self.repeated_character_match_mode
        {
            root_walker_builder =
                root_walker_builder.callbacks(vec![ContextualizedNode::InDirectPath(&self.root)]);
        }
        let root_walker = root_walker_builder.build();
        let alias_walkers = root_walker.branch_to_aliases(&mut HashSet::new());
        let mut walkers: Vec<Walker> = if let RepeatedCharacterMatchMode::AllowRepeatedCharacters =
            self.repeated_character_match_mode
        {
            alias_walkers
                .map(|mut walker| {
                    walker
                        .callbacks
                        .push(ContextualizedNode::InSubgraph(&self.root));
                    walker
                })
                .collect()
        } else {
            root_walker.branch_to_aliases(&mut HashSet::new()).collect()
        };
        walkers.push(root_walker);

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
                        let alias_walkers = walker.branch_to_aliases(&mut HashSet::new());
                        if let RepeatedCharacterMatchMode::AllowRepeatedCharacters =
                            self.repeated_character_match_mode
                        {
                            new_walkers.extend(alias_walkers.map(|mut inner_walker| {
                                inner_walker
                                    .callbacks
                                    .push(ContextualizedNode::InSubgraph(walker.node));
                                inner_walker
                            }));
                        } else {
                            new_walkers.extend(alias_walkers);
                        }

                        // Graphemes.
                        let grapheme_walkers =
                            walker.branch_to_grapheme_subgraphs(&mut HashSet::new());
                        if let RepeatedCharacterMatchMode::AllowRepeatedCharacters =
                            self.repeated_character_match_mode
                        {
                            new_walkers.extend(grapheme_walkers.map(|mut inner_walker| {
                                inner_walker
                                    .callbacks
                                    .push(ContextualizedNode::InSubgraph(walker.node));
                                inner_walker
                            }))
                        } else {
                            new_walkers.extend(grapheme_walkers);
                        }

                        // Separators.
                        let mut separator_walker = walker.clone();
                        separator_walker.node = &self.separator_root;
                        separator_walker.returns.push(walker.node);
                        separator_walker.in_separator = true;
                        if let RepeatedCharacterMatchMode::AllowRepeatedCharacters =
                            self.repeated_character_match_mode
                        {
                            separator_walker
                                .callbacks
                                .push(ContextualizedNode::InSubgraph(walker.node));
                            separator_walker
                                .targets
                                .push(ContextualizedNode::InSubgraph(walker.node));
                        }
                        new_walkers.push(separator_walker);

                        // Direct path.
                        if let RepeatedCharacterMatchMode::AllowRepeatedCharacters =
                            self.repeated_character_match_mode
                        {
                            walker
                                .callbacks
                                .push(ContextualizedNode::InDirectPath(walker.node));
                        }
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
            let root_walker = WalkerBuilder::new(&self.root).start(i + 1).build();
            new_walkers.extend(root_walker.branch_to_aliases(&mut HashSet::new()));
            new_walkers.extend(root_walker.branch_to_grapheme_subgraphs(&mut HashSet::new()));
            new_walkers.push(root_walker);

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
    pub fn find(&self, input: &str) -> Box<[&str]> {
        self.find_walkers(input)
            .map(|walker| {
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

            output.push_str(&(self.censor)(&input[substring_start..substring_end]));

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
}

impl fmt::Debug for WordFilter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WordFilter")
            .field("root", &self.root)
            .field("separator_root", &self.separator_root)
            .field("_alias_map", &self._alias_map)
            .field(
                "repeated_character_match_mode",
                &self.repeated_character_match_mode,
            )
            .field("censor", &(self.censor as usize as *const ()))
            .finish()
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
/// [`censor::replace_graphemes_with!("*")`].
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
///     .censor(censor::replace_graphemes_with!("#"))
///     .build();
/// ```
///
/// [`words`]: Self::words
/// [`exceptions`]: Self::exceptions
/// [`separators`]: Self::separators
/// [`aliases`]: Self::aliases
/// [`repeated_character_match_mode`]: Self::repeated_character_match_mode
/// [`censor`]: Self::censor
/// [`censor::replace_graphemes_with!("*")`]: censor/macro.replace_graphemes_with.html
#[derive(Clone)]
pub struct WordFilterBuilder<'a> {
    words: Vec<String>,
    exceptions: Vec<String>,
    separators: Vec<String>,
    aliases: Vec<(String, String)>,
    repeated_character_match_mode: RepeatedCharacterMatchMode,
    censor: fn(&str) -> String,
    _phantom_lifetime: PhantomData<&'a ()>,
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
            censor: replace_graphemes_with!("*"),
            _phantom_lifetime: PhantomData,
        }
    }

    /// Adds a word to be used in building the [`WordFilter`].
    ///
    /// Note that this does not replace any words that have been added prior. Multiple calls to this
    /// method will result in all words being used.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().word("foo").build();
    /// ```
    #[inline]
    pub fn word<S>(&mut self, word: S) -> &mut Self
    where
        S: ToString,
    {
        self.words.push(word.to_string());
        self
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
    pub fn words<I, S>(&mut self, words: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: ToString,
    {
        self.words.extend(words.into_iter().map(|s| s.to_string()));
        self
    }

    /// Adds an exception to be used in building the [`WordFilter`].
    ///
    /// Note that this does not replace any exceptions that have been added prior. Multiple calls to
    /// this method will result in all exceptions being used.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().exception("foo").build();
    /// ```
    #[inline]
    pub fn exception<S>(&mut self, exception: S) -> &mut Self
    where
        S: ToString,
    {
        self.exceptions.push(exception.to_string());
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
    pub fn exceptions<I, S>(&mut self, exceptions: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: ToString,
    {
        self.exceptions
            .extend(exceptions.into_iter().map(|s| s.to_string()));
        self
    }

    /// Adds a separator to be used in building the [`WordFilter`].
    ///
    /// Note that this does not replace any separators that have been added prior. Multiple calls to
    /// this method will result in all separators being used.
    ///
    /// # Example
    /// ```
    /// use word_filter::WordFilterBuilder;
    ///
    /// let filter = WordFilterBuilder::new().separator("_").build();
    /// ```
    #[inline]
    pub fn separator<S>(&mut self, separator: S) -> &mut Self
    where
        S: ToString,
    {
        self.separators.push(separator.to_string());
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
    pub fn separators<I, S>(&mut self, separators: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: ToString,
    {
        self.separators
            .extend(separators.into_iter().map(|s| s.to_string()));
        self
    }

    /// Adds an alias to be used in building the [`WordFilter`].
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
    /// let filter = WordFilterBuilder::new().alias(("a", "@")).build();
    /// ```
    #[inline]
    pub fn alias<S, T>(&mut self, alias: (S, T)) -> &mut Self
    where
        S: ToString,
        T: ToString,
    {
        self.aliases
            .push((alias.0.to_string(), alias.1.to_string()));
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
    pub fn aliases<'b, I, S, T>(&mut self, aliases: I) -> &mut Self
    where
        I: IntoIterator<Item = &'b (S, T)>,
        S: ToString + 'b,
        T: ToString + 'b,
    {
        self.aliases.extend(
            aliases
                .into_iter()
                .map(|(s, t)| (s.to_string(), t.to_string())),
        );
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
    /// default censor is [`censor::replace_graphemes_with!("*")`].
    ///
    /// # Example
    /// ```
    /// use word_filter::{censor, WordFilterBuilder};
    ///
    /// let filter = WordFilterBuilder::new().censor(censor::replace_graphemes_with!("#")).build();
    /// ```
    ///
    /// [`censor::replace_graphemes_with!("*")`]: censor/macro.replace_graphemes_with.html
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
                    .entry(value.clone())
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
                    value.clone(),
                    unsafe {
                        // SAFETY: `overlap_value` will always be the prefix of `merge_value`.
                        // Therefore, this will never be out of bounds and it will always uphold
                        // `str` invariants.
                        merge_value.get_unchecked(overlap_value.len()..).to_owned()
                    },
                    alias.clone(),
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
                            debug_unreachable!()
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

impl fmt::Debug for WordFilterBuilder<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WordFilterBuilder")
            .field("words", &self.words)
            .field("exceptions", &self.exceptions)
            .field("separators", &self.separators)
            .field("aliases", &self.aliases)
            .field(
                "repeated_character_match_mode",
                &self.repeated_character_match_mode,
            )
            .field("censor", &(self.censor as usize as *const ()))
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::{replace_graphemes_with, RepeatedCharacterMatchMode, WordFilterBuilder};
    use alloc::{vec, vec::Vec};

    #[test]
    fn builder_word() {
        let filter = WordFilterBuilder::new().word("foo").build();

        assert!(filter.check("foo"));
    }

    #[test]
    fn builder_exception() {
        let filter = WordFilterBuilder::new()
            .word("foo")
            .exception("foobar")
            .build();

        assert!(filter.check("foo"));
        assert!(!filter.check("foobar"));
    }

    #[test]
    fn builder_separator() {
        let filter = WordFilterBuilder::new().word("foo").separator(" ").build();

        assert!(filter.check("f o o"));
    }

    #[test]
    fn builder_alias() {
        let filter = WordFilterBuilder::new()
            .word("foo")
            .alias(("f", "F"))
            .build();

        assert!(filter.check("Foo"));
    }

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
            .censor(replace_graphemes_with!("#"))
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

    #[test]
    fn censor_repeated_alias() {
        let filter = WordFilterBuilder::new()
            .words(&["foo", "bar"])
            .aliases(&[("a", "A")])
            .build();

        assert_eq!(filter.censor("fbaAaAaAar"), "f*********");
    }

    #[test]
    fn separator_in_match_filled_with_smaller_match() {
        let filter = WordFilterBuilder::new()
            .words(&["foobar"])
            .separators(&[" "])
            .aliases(&[("bar", "baz")])
            .build();

        assert_eq!(filter.find("foo baz"), vec!["foobar"].into_boxed_slice());
    }

    #[test]
    fn repeated_graphemes() {
        let filter = WordFilterBuilder::new().words(&["bãr"]).build();

        assert_eq!(filter.find("bããr"), vec!["bãr"].into_boxed_slice());
    }

    #[test]
    fn grapheme_in_alias() {
        let filter = WordFilterBuilder::new()
            .words(&["bar"])
            .aliases(&[("a", "ã")])
            .build();

        assert_eq!(filter.find("bãr"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn alias_on_grapheme() {
        let filter = WordFilterBuilder::new()
            .words(&["bãr"])
            .aliases(&[("ã", "õ")])
            .build();

        assert_eq!(filter.find("bõr"), vec!["bãr"].into_boxed_slice());
    }
}
