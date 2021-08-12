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
//! [`WordFilter`]s must be created at compile-time using a
//! [build script](https://doc.rust-lang.org/cargo/reference/build-scripts.html) using the tools
//! provided in the [`codegen`] module. The generated code can then be [`include!`]ed and used.
//!
//! ## Example
//! For example, a simple [`WordFilter`] can be generated by the following.
//!
//! First, add the `word_filter` crate to both the `Cargo.toml` `[dependencies]` and
//! `[build-dependencies]` lists.
//!
//! ``` toml
//! ...
//! [dependencies]
//! word_filter = "0.7.0"
//!
//! [build-dependencies]
//! word_filter = "0.7.0"
//! ...
//! ```
//!
//! Next, generate the [`WordFilter`] in the `build.rs` file.
//!
//! ``` no_run
//! use std::{
//!     env,
//!     fs::File,
//!     io::{BufWriter, Write},
//!     path::Path,
//! };
//! use word_filter::codegen::{Visibility, WordFilterGenerator};
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
pub mod codegen;
pub mod pda;

mod constants;

use alloc::{string::String, vec, vec::Vec};
use constants::{EXCEPTION_INDEX, SEPARATOR_INDEX, WORD_INDEX};
use core::{cmp, iter::FromIterator};
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
/// `WordFilter`s are constructed at compile-time using the [`codegen`] module. See crate-level
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
        let mut ids = vec![
            InstantaneousDescription::new(&self.states[WORD_INDEX], start),
            InstantaneousDescription::new(&self.states[EXCEPTION_INDEX], start),
        ];

        ids.extend(
            ids.iter()
                .map(|id| id.transition(None, &self.states[SEPARATOR_INDEX]))
                .flatten()
                .collect::<Vec<_>>(),
        );
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
            let mut first_c = true;
            for c in grapheme.chars() {
                let mut new_ids = Vec::new();
                for id in ids.drain(..) {
                    new_ids.extend(id.step(c, &self.states[SEPARATOR_INDEX], first_c));
                }
                index += c.len_utf8();
                ids = new_ids;
                first_c = false;
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
    /// use word_filter::codegen::{Visibility, WordFilterGenerator};
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
    #[must_use]
    pub fn find(&'a self, input: &str) -> impl Iterator<Item = &str> {
        self.compute(input).map(|id| unsafe {
            // SAFETY: Each item returned from `self.compute()` is guaranteed to contain a word.
            id.unwrap_word_unchecked()
        })
    }

    /// Find all raw string slices matched in `input`.
    ///
    /// Returns an iterator over all matched slices in `input`.
    ///
    /// /// # Example
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
    /// use word_filter::codegen::{Visibility, WordFilterGenerator};
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
    ///             .alias('o', 'a')
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
    /// assert_eq!(FILTER.find_raw("this string contains fao").collect::<Vec<_>>(), vec!["fao"]);
    /// ```
    ///
    /// [`Iterator`]: core::iter::Iterator
    #[inline]
    #[must_use]
    pub fn find_raw<'b, 'c>(&'a self, input: &'b str) -> impl Iterator<Item = &'c str>
    where
        'a: 'c,
        'b: 'c,
    {
        self.compute(input).map(move |id| unsafe {
            // SAFETY: The `start` and `end` in `id` are guaranteed to be on UTF8
            // bounds of `input`, since `id` is generated during `compute()` using the `char`s
            // in `input`.
            input.get_unchecked(id.start()..id.end())
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
    /// use word_filter::codegen::{Visibility, WordFilterGenerator};
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
    /// use word_filter::codegen::{Visibility, WordFilterGenerator};
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

        for id in self.compute(input) {
            if id.start() > prev_end {
                output.push_str(unsafe {
                    // SAFETY: Both `prev_end` and `id.start()` are guaranteed to be on valid UTF-8
                    // boundaries of `input`.
                    input.get_unchecked(prev_end..id.start())
                });
            }
            // Censor the covered characters for this ID.
            output.push_str(&(censor)(unsafe {
                // SAFETY: `id.start()`, `id.end()`, and `prev_end` are all guaranteed to be on
                // valid UTF-8 boundaries of `input`.
                input.get_unchecked(cmp::max(id.start(), prev_end)..id.end())
            }));
            prev_end = id.end();
        }
        output.push_str(unsafe {
            // SAFETY: `prev_end` is guaranteed to be on a valid UTF-8 boundary of `input`.
            input.get_unchecked(prev_end..)
        });
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
    /// use word_filter::codegen::{Visibility, WordFilterGenerator};
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
