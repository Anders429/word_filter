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
//! [`WordFilter`]s must be created at compile-time using the
//! [`word_filter_codegen`](https://docs.rs/word_filter_codegen) crate. The generated code can then
//! be [`include!`]ed and used.
//!
//! ## Example
//! For example, a simple [`WordFilter`] can be generated by the following.
//!
//! First, add both the `word_filter` and `word_filter_codegen` crates to the `Cargo.toml`
//! `[dependencies]` and `[build-dependencies]` lists respectively.
//!
//! ``` toml
//! ...
//! [dependencies]
//! word_filter = "0.5.0"
//! 
//! [build-dependencies]
//! word_filter_codegen = "0.5.0"
//! ...
//! ```
//!
//! Next, generate the [`WordFilter`] in the `build.rs` file.
//!
//! ``` ignore
//! use std::{
//!     env,
//!     fs::File,
//!     io::{BufWriter, Write},
//!     path::Path,
//! };
//! use word_filter_codegen::{Visibility, WordFilterGenerator};
//!
//! fn main() {
//!     let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
//!     let mut file = BufWriter::new(File::create(&path).unwrap());
//!
//!     writeln!(
//!         &mut file,
//!         "{}",
//!         WordFilterGenerator::new()
//!             .visibility(Visibility::Pub)
//!             .word("foo")
//!             .generate("FILTER")
//!         );
//! }
//! ```
//!
//! And finally, include the generated code in the `lib.rs` file.
//!
//! ``` ignore
//! include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
//!
//! assert!(FILTER.censor("Should censor foo."), "Should censor ***.");
//! ```

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

/// A word filter for identifying filtered words within strings.
///
/// A `WordFilter` is constructed from **filtered words**, **exceptions**, **separators**,
/// and **aliases**. Each of those parameters are defined as follows:
///
/// - **filtered words** - strings that should be identified and censored by the `WordFilter`.
/// - **exceptions** - strings that should explicitly not be identified and censored by the
/// `WordFilter`. Any string that contains filtered word that is contained entirely inside an
/// exception will be ignored.
/// - **separators** - strings that may appear between characters in filtered words and exceptions.
/// - **aliases** - tuples defining alias strings that may replace source strings during matching.
/// These are of the form `(<source string>, <alias string>)`.
///
/// `WordFilter`s are constructed at compile-time using the
/// [`word_filter_codegen`](https://docs.rs/word_filter_codegen) crate. See crate-level 
/// documentation for further information.
#[derive(Debug)]
pub struct WordFilter<'a, const N: usize> {
    #[doc(hidden)]
    pub root: Node<'a>,
    #[doc(hidden)]
    pub separator_root: Node<'a>,
    #[doc(hidden)]
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
        walkers.extend(root_walker.branch_to_alias_subgraphs().map(|mut walker| {
            walker
                .callbacks
                .push(ContextualizedNode::InSubgraph(&self.root));
            walker
        }));
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
                        let grapheme_walkers = walker.branch_to_grapheme_subgraphs();
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
    /// Returns an [`Iterator`] over all matched filtered words.
    ///
    /// # Example
    ///
    /// Assuming a compile-time constructed `WordFilter` `FILTER`, defined in a `build.rs` as:
    ///
    /// ``` ignore
    /// use std::{
    ///     env,
    ///     fs::File,
    ///     io::{BufWriter, Write},
    ///     path::Path,
    /// };
    /// use word_filter_codegen::{Visibility, WordFilterGenerator};
    ///
    /// fn main() {
    ///     let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    ///     let mut file = BufWriter::new(File::create(&path).unwrap());
    ///
    ///     writeln!(
    ///         &mut file,
    ///         "{}",
    ///         WordFilterGenerator::new()
    ///             .word("foo")
    ///             .generate("FILTER")
    ///         );
    /// }
    /// ```
    ///
    /// this method is used as follows:
    ///
    /// ``` ignore
    /// include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
    ///
    /// assert_eq!(FILTER.find("this string contains foo").collect::<Vec<_>>(), vec!["foo"]);
    /// ```
    ///
    /// [`Iterator`]: core::iter::Iterator
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
    /// # Example
    /// 
    /// Assuming a compile-time constructed `WordFilter` `FILTER`, defined in a `build.rs` as:
    ///
    /// ``` ignore
    /// use std::{
    ///     env,
    ///     fs::File,
    ///     io::{BufWriter, Write},
    ///     path::Path,
    /// };
    /// use word_filter_codegen::{Visibility, WordFilterGenerator};
    ///
    /// fn main() {
    ///     let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    ///     let mut file = BufWriter::new(File::create(&path).unwrap());
    ///
    ///     writeln!(
    ///         &mut file,
    ///         "{}",
    ///         WordFilterGenerator::new()
    ///             .word("foo")
    ///             .generate("FILTER")
    ///         );
    /// }
    /// ```
    ///
    /// this method is used as follows:
    ///
    /// ``` ignore
    /// include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
    ///
    /// assert!(FILTER.check("this string contains foo"));
    /// ```
    #[must_use]
    pub fn check(&self, input: &str) -> bool {
        self.find_walkers(input).next().is_some()
    }

    /// Censor all filtered words within `input`, replacing their occurances with the output of
    /// `censor`.
    ///
    /// Returns a newly-allocated `String` with all filtered words censored.
    ///
    /// # Example
    /// Assuming a compile-time constructed `WordFilter` `FILTER`, defined in a `build.rs` as:
    ///
    /// ``` ignore
    /// use std::{
    ///     env,
    ///     fs::File,
    ///     io::{BufWriter, Write},
    ///     path::Path,
    /// };
    /// use word_filter_codegen::{Visibility, WordFilterGenerator};
    ///
    /// fn main() {
    ///     let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    ///     let mut file = BufWriter::new(File::create(&path).unwrap());
    ///
    ///     writeln!(
    ///         &mut file,
    ///         "{}",
    ///         WordFilterGenerator::new()
    ///             .word("foo")
    ///             .generate("FILTER")
    ///         );
    /// }
    /// ```
    ///
    /// this method is used as follows:
    ///
    /// ``` ignore
    /// use word_filter::censor;
    ///
    /// include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
    ///
    /// assert!(
    ///     FILTER.censor_with("this string contains foo", censor::replace_graphemes_with!("#")),
    ///     "this string contains ###"
    /// );
    /// ```
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

    /// Censor all filtered words within `input` with a default censor of
    /// [`censor::replace_graphemes_with("*")`].
    ///
    /// Returns a newly-allocated `String` with all filtered words censored.
    ///
    /// # Example
    /// Assuming a compile-time constructed `WordFilter` `FILTER`, defined in a `build.rs` as:
    ///
    /// ``` ignore
    /// use std::{
    ///     env,
    ///     fs::File,
    ///     io::{BufWriter, Write},
    ///     path::Path,
    /// };
    /// use word_filter_codegen::{Visibility, WordFilterGenerator};
    ///
    /// fn main() {
    ///     let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    ///     let mut file = BufWriter::new(File::create(&path).unwrap());
    ///
    ///     writeln!(
    ///         &mut file,
    ///         "{}",
    ///         WordFilterGenerator::new()
    ///             .word("foo")
    ///             .generate("FILTER")
    ///         );
    /// }
    /// ```
    ///
    /// this method is used as follows:
    ///
    /// ``` ignore
    /// include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
    ///
    /// assert!(FILTER.censor("this string contains foo"), "this string contains ***");
    /// ```
    ///
    /// [`censor::replace_graphemes_with("*")`]: censor/macro.replace_graphemes_with.html
    #[cfg(feature = "unicode-segmentation")]
    #[inline]
    #[must_use]
    pub fn censor(&self, input: &str) -> String {
        self.censor_with(input, censor::replace_graphemes_with!("*"))
    }
}
