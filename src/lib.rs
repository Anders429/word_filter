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
//! word_filter = "0.6.0"
//!
//! [build-dependencies]
//! word_filter_codegen = "0.6.0"
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
pub mod pda;

use alloc::{string::String, vec::Vec};
use core::{cmp, iter::FromIterator};
use debug_unreachable::debug_unreachable;
use hashbrown::HashSet;
use nested_containment_list::NestedContainmentList;
use pda::{InstantaneousDescription, State};
use unicode_segmentation::UnicodeSegmentation;

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
    pub states: [State<'a>; N],
}

impl<'a, const N: usize> WordFilter<'a, N> {
    /// Create all entry instantaneous descriptions.
    ///
    /// This includes the standard entry state and all of its ε-transitions.
    fn spawn_entry_ids(
        &'a self,
        start: usize,
    ) -> impl Iterator<Item = InstantaneousDescription<'_>> {
        let mut ids = Vec::new();
        ids.push(InstantaneousDescription::new(&self.states[0], start));
        ids.extend(ids[0].transition(None, &mut HashSet::new()));
        ids.into_iter()
    }

    /// Run the computation, finding all matched words within `input`.
    fn compute(&'a self, input: &str) -> impl Iterator<Item = InstantaneousDescription<'_>> {
        let mut ids = Vec::new();
        let mut accepted_ids = Vec::new();
        let mut index = 0;
        // Handle the input one grapheme at a time. Only accepting states found at the end of
        // graphemes are kept.
        for grapheme in input.graphemes(true) {
            ids.extend(self.spawn_entry_ids(index));
            for c in grapheme.chars() {
                let mut new_ids = Vec::new();
                for instant in ids.drain(..) {
                    new_ids.extend(instant.step(c));
                }
                index += 1;
                ids = new_ids;
            }
            // Now that all characters within the grapheme have been processed, determine if any
            // ids are in an accepting state.
            for id in &ids {
                if id.is_accepting() {
                    accepted_ids.push(id.clone());
                }
            }
        }
        // Return outer-most nested words, ignoring words and exceptions nested within.
        NestedContainmentList::from_iter(accepted_ids)
            .into_iter()
            .filter_map(|element| {
                let instant = element.value;
                if instant.is_word() {
                    Some(instant)
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
    #[inline]
    pub fn find(&'a self, input: &str) -> impl Iterator<Item = &str> {
        self.compute(input)
            .map(|id| unsafe { id.unwrap_word_unchecked() })
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
    #[inline]
    #[must_use]
    pub fn check(&'a self, input: &str) -> bool {
        self.compute(input).next().is_some()
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
    pub fn censor_with(&'a self, input: &str, censor: fn(&str) -> String) -> String {
        let mut output = String::with_capacity(input.len());
        let mut prev_end = 0;
        let mut chars = input.chars();

        for id in self.compute(input) {
            if id.start() > prev_end {
                for _ in 0..(id.start() - prev_end) {
                    output.push(match chars.next() {
                        Some(c) => c,
                        None => unsafe { debug_unreachable!() },
                    })
                }
            }
            // Censor the covered characters for this ID.
            output.push_str(&(censor)(
                &chars
                    .by_ref()
                    .take(id.end() - cmp::max(id.start(), prev_end))
                    .collect::<String>(),
            ));
            prev_end = id.end();
        }
        output.push_str(chars.as_str());
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
    #[inline]
    #[must_use]
    pub fn censor(&'a self, input: &str) -> String {
        self.censor_with(input, censor::replace_graphemes_with!("*"))
    }
}
