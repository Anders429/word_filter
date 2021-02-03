//! A robust implementation of a Word Filter.
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
//! An example of a functional Word Filter using this crate is as follows:
//!
//! ```
//! use word_filter::{Options, WordFilter};
//!
//! // Filtered words are words that should be detected by the WordFilter.
//! let filtered_words = &["foo"];
//! // Exceptions are words that should not be detected by the WordFilter, even if words inside them
//! // are.
//! let exceptions = &["foobar"];
//! // Separators are characters that can appear between letters within filtered words.
//! let separators = &[" ", "_"];
//! // Aliases define characters that can be found in place of other characters in a match.
//! let aliases = &[("f", "F")];
//!
//! // All of these together are used to create a WordFilter.
//! let word_filter = WordFilter::new(
//!     filtered_words,
//!     exceptions,
//!     separators,
//!     aliases,
//!     Options::default(),
//! );
//!
//! // The word filter will both identify and censor the word "foo".
//! assert!(word_filter.check("Should censor foo"));
//! assert_eq!(word_filter.censor("Should censor foo"), "Should censor ***");
//!
//! // The word filter does not identify or censor the word "foobar".
//! assert!(!word_filter.check("Should not censor foobar"));
//! assert_eq!(word_filter.censor("Should not censor foobar"), "Should not censor foobar");
//!
//! // The word filter will ignore separators while matching.
//! assert!(word_filter.check("Should censor f o_o"));
//! assert_eq!(word_filter.censor("Should censor f o_o"), "Should censor *****");
//!
//! // The word filter checks for aliases while matching.
//! assert!(word_filter.check("Should censor Foo"));
//! assert_eq!(word_filter.censor("Should censor Foo"), "Should censor ***");
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
// The following clippy allowances are due to the MSRV of this crate being less than the required
// MSRV for each lint. The required MSRV for each lint is listed below. If the MSRV is bumped enough
// to allow usage of a lint, it should be removed from this list.
// NOTE: This will no longer be necessary with the next stable release (1.50.0), as the MSRV
// specification can be placed in a config file at that point..
//
// Required MSRVs:
// - manual_strip: 1.45.0
// - match_like_matches_macro: 1.42.0
// - nursery::use_self: 1.37.0
#![allow(
    clippy::manual_strip,
    clippy::match_like_matches_macro,
    clippy::nursery::use_self
)]
// This lint is directly contradictory to `unreachable_pub`.
#![allow(clippy::nursery::redundant_pub_crate)]
#![no_std]

extern crate alloc;

mod node;
mod pointer;

use alloc::{borrow::ToOwned, boxed::Box, collections::VecDeque, string::String, vec, vec::Vec};
use by_address::ByAddress;
use core::pin::Pin;
use hashbrown::{HashMap, HashSet};
use nested_containment_list::{Interval, NestedContainmentList};
use node::Node;
use pointer::Pointer;
use str_overlap::Overlap;
use unchecked_unwrap::UncheckedUnwrap;

/// The strategy a `WordFilter` should use to match repeated characters.
pub enum RepeatedCharacterMatchMode {
    /// Allows repeated characters within filtered words.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{CensorMode, Options, RepeatedCharacterMatchMode, WordFilter};
    ///
    /// let word_filter = WordFilter::new(&["bar"], &[], &[], &[], Options {
    ///     repeated_character_match_mode: RepeatedCharacterMatchMode::AllowRepeatedCharacters,
    ///     censor_mode: CensorMode::default(),   
    /// });
    ///
    /// assert!(word_filter.check("baaar"));
    /// ```
    AllowRepeatedCharacters,
    /// Disallows repeated characters within filtered words.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{CensorMode, Options, RepeatedCharacterMatchMode, WordFilter};
    ///
    /// let word_filter = WordFilter::new(&["bar"], &[], &[], &[], Options {
    ///     repeated_character_match_mode: RepeatedCharacterMatchMode::DisallowRepeatedCharacters,
    ///     censor_mode: CensorMode::default(),   
    /// });
    ///
    /// assert!(!word_filter.check("baaar"));
    /// ```
    DisallowRepeatedCharacters,
}

impl Default for RepeatedCharacterMatchMode {
    /// Returns the default mode, which is `AllowRepeatedCharacters`.
    fn default() -> Self {
        RepeatedCharacterMatchMode::AllowRepeatedCharacters
    }
}

/// The strategy for censoring in a `WordFilter`.
pub enum CensorMode {
    /// Replace all matched characters with the character indicated.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{CensorMode, Options, RepeatedCharacterMatchMode, WordFilter};
    ///
    /// let word_filter = WordFilter::new(&["foo"], &[], &[], &[], Options {
    ///     repeated_character_match_mode: RepeatedCharacterMatchMode::default(),
    ///     censor_mode: CensorMode::ReplaceAllWith('*'),   
    /// });
    ///
    /// assert_eq!(word_filter.censor("foo"), "***");
    /// ```
    ReplaceAllWith(char),
}

impl Default for CensorMode {
    /// Returns the default mode, which is `ReplaceAllWith('*')`.
    fn default() -> Self {
        CensorMode::ReplaceAllWith('*')
    }
}

/// Options for `WordFilter`s.
///
/// This specifies both the `RepeatedCharacterMatchMode` and the `CensorMode` for a `WordFilter`.
///
/// Example usage:
///
/// ```
/// use word_filter::{CensorMode, Options, RepeatedCharacterMatchMode, WordFilter};
///
/// let word_filter = WordFilter::new(&["bar"], &[], &[], &[], Options {
///     repeated_character_match_mode: RepeatedCharacterMatchMode::AllowRepeatedCharacters,
///     censor_mode: CensorMode::ReplaceAllWith('*'),   
/// });
///
/// assert_eq!(word_filter.censor("baaar"), "*****");
/// ```
#[derive(Default)]
pub struct Options {
    /// The strategy used for matching repeated characters.
    pub repeated_character_match_mode: RepeatedCharacterMatchMode,
    /// The strategy used for censoring.
    pub censor_mode: CensorMode,
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
/// use word_filter::{Options, WordFilter};
///
/// let filtered_words = &["foo"];
/// let exceptions = &["foobar"];
/// let separators = &[" ", "_"];
/// let aliases = &[("f", "F")];
///
/// let word_filter = WordFilter::new(
///     filtered_words,
///     exceptions,
///     separators,
///     aliases,
///     Options::default(),
/// );
///
/// assert_eq!(word_filter.censor("fff ooo_o foobar"), "********* foobar");
/// ```
pub struct WordFilter<'a> {
    root: Node<'a>,
    separator_root: Node<'a>,
    _alias_map: HashMap<String, Pin<Box<Node<'a>>>>,
    options: Options,
}

impl<'a> WordFilter<'a> {
    /// Create a new `WordFilter`.
    ///
    /// Note that `WordFilter`s created this way are immutable after their creation. Once you
    /// specify the filtered words, exceptions, separators, aliases, and options, they can not be
    /// changed.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{Options, WordFilter};
    ///
    /// let filtered_words = &["foo"];
    /// let exceptions = &["foobar"];
    /// let separators = &[" ", "_"];
    /// let aliases = &[("f", "F")];
    ///
    /// let word_filter = WordFilter::new(
    ///     filtered_words,
    ///     exceptions,
    ///     separators,
    ///     aliases,
    ///     Options::default(),
    /// );
    /// ```
    #[must_use]
    pub fn new(
        filtered_words: &[&'a str],
        exceptions: &[&'a str],
        separators: &[&str],
        aliases: &[(&'a str, &str)],
        options: Options,
    ) -> Self {
        let mut root = Node::new();

        for word in filtered_words {
            root.add_match(word);
        }

        for word in exceptions {
            root.add_exception(word);
        }

        let mut separator_root = Node::new();
        for word in separators {
            separator_root.add_return(word);
        }

        let mut alias_map = HashMap::new();
        for (value, alias) in aliases {
            unsafe {
                // SAFETY: Adding an alias to a `Node` will not move the `Node`. Therefore, this
                // mutation of the `Node` will uphold pin invariants.
                alias_map
                    .entry((*value).to_owned())
                    .or_insert_with(|| Box::pin(Node::new()))
                    .as_mut()
                    .get_unchecked_mut()
                    .add_return(alias);
            }
        }
        // Find merged aliases.
        // First, find all aliases that can possibly be combined by a value.
        let mut queue = VecDeque::new();
        for (value, alias) in aliases {
            for (merge_value, _) in aliases {
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
            for (new_value, new_alias) in aliases {
                if target_value == *new_alias || new_alias.starts_with(&target_value) {
                    new_aliases.push((value.to_owned() + new_value, alias.to_owned() + new_alias));
                } else if target_value.starts_with(new_alias) {
                    // If the combination isn't complete, push it to the queue and try again.
                    queue.push_back((
                        value.to_owned() + new_value,
                        unsafe {
                            // SAFETY: Since `new_alias` is the prefix of `target_value`, this will
                            // never be out of bounds and will always uphold `str` invariants.
                            target_value.get_unchecked(new_alias.len()..).to_owned()
                        },
                        alias.to_owned() + new_alias,
                    ));
                }
            }
        }
        for (value, alias) in new_aliases {
            unsafe {
                // SAFETY: Adding a return to a `Node` will not move the `Node`. Therefore, this
                // mutation of the `Node` will uphold pin invariants.
                alias_map
                    .entry(value)
                    .or_insert_with(|| Box::pin(Node::new()))
                    .as_mut()
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
                    alias_map
                        .get_mut(value)
                        // SAFETY: We know that `value` is a valid key in `alias_map`, and therefore
                        // `get_mut()` will always return a value.
                        .unchecked_unwrap()
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

        Self {
            root,
            separator_root,
            _alias_map: alias_map,
            options,
        }
    }

    /// Create new `Pointer`s for the aliases at the `pointer`'s `current_node`.
    fn push_aliases(
        &self,
        pointer: &Pointer<'a>,
        new_pointers: &mut Vec<Pointer<'a>>,
        visited: &mut HashSet<ByAddress<&Node<'a>>>,
    ) {
        for (alias_node, return_node) in &pointer.current_node.aliases {
            if visited.contains(&ByAddress(alias_node)) {
                continue;
            }
            let mut return_nodes = pointer.return_nodes.clone();
            return_nodes.push(return_node);
            let alias_pointer =
                Pointer::new(alias_node, return_nodes, pointer.start, pointer.len, false);
            visited.insert(ByAddress(alias_node));
            self.push_aliases(&alias_pointer, new_pointers, visited);
            visited.remove(&ByAddress(alias_node));
            new_pointers.push(alias_pointer);
        }
    }

    /// Finds all `Pointer`s that encounter matches.
    ///
    /// This also excludes all `Pointer`s that encountered matches but whose ranges also are
    /// contained within ranges are `Pointer`s who encountered exceptions.
    fn find_pointers(&self, input: &str) -> Box<[Pointer<'_>]> {
        let root_pointer = Pointer::new(&self.root, Vec::new(), 0, 0, false);
        let mut pointers = Vec::new();
        self.push_aliases(&root_pointer, &mut pointers, &mut HashSet::new());
        pointers.push(root_pointer);
        let mut found = Vec::new();
        for (i, c) in input.chars().enumerate() {
            let mut new_pointers = Vec::new();
            for mut pointer in pointers.drain(..) {
                let mut last_pointer = pointer.clone();
                if pointer.step(c) {
                    // Aliases.
                    self.push_aliases(&pointer, &mut new_pointers, &mut HashSet::new());
                    // Separators.
                    let mut return_nodes = pointer.return_nodes.clone();
                    return_nodes.push(pointer.current_node);
                    new_pointers.push(Pointer::new(
                        &self.separator_root,
                        return_nodes,
                        pointer.start,
                        pointer.len,
                        true,
                    ));

                    // Direct path.
                    new_pointers.push(pointer);

                    // Repeated characters.
                    if let RepeatedCharacterMatchMode::AllowRepeatedCharacters =
                        self.options.repeated_character_match_mode
                    {
                        last_pointer.len += 1;
                        new_pointers.push(last_pointer);
                    }
                } else if let pointer::Status::Match(_) = pointer.status {
                    found.push(pointer);
                } else if let pointer::Status::Exception(_) = pointer.status {
                    found.push(pointer);
                }
            }

            // Add root again.
            new_pointers.push(Pointer::new(&self.root, Vec::new(), i + 1, 0, false));
            new_pointers.extend(self.root.aliases.iter().map(|(alias_node, return_node)| {
                Pointer::new(alias_node, vec![return_node], i + 1, 0, false)
            }));

            pointers = new_pointers;
        }

        // Evaluate all remaining pointers.
        for pointer in pointers.drain(..) {
            match pointer.status {
                pointer::Status::Match(_) | pointer::Status::Exception(_) => found.push(pointer),
                pointer::Status::None => {}
            }
        }

        // Only return outer-most matched words which aren't part of a longer exception.
        NestedContainmentList::from_slice(&found)
            .sublist()
            .map(|element| element.value)
            .filter_map(|p| {
                if let pointer::Status::Match(_) = p.status {
                    Some(p.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .into_boxed_slice()
    }

    /// Find all filtered words matched by `input`.
    ///
    /// Returns a boxed slice containing all matched filtered words in order of appearance.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{Options, WordFilter};
    ///
    /// let word_filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());
    ///
    /// assert_eq!(word_filter.find("this string contains foo"), vec!["foo"].into_boxed_slice());
    /// ```
    #[must_use]
    pub fn find(&self, input: &str) -> Box<[&str]> {
        self.find_pointers(input)
            .iter()
            .map(|pointer| {
                if let pointer::Status::Match(s) = pointer.status {
                    s
                } else {
                    unreachable!()
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
    /// use word_filter::{Options, WordFilter};
    ///
    /// let word_filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());
    ///
    /// assert!(word_filter.check("this string contains foo"));
    /// ```
    #[must_use]
    pub fn check(&self, input: &str) -> bool {
        !self.find_pointers(input).is_empty()
    }

    /// Censor all filtered words within `input`.
    ///
    /// Returns a newly-allocated `String` with all filtered words censored using the `CensorMode`
    /// strategy, as defined in the `Options` passed to the `WordFilter` at construction.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{Options, WordFilter};
    ///
    /// // Note that Options::default() uses CensorMode::ReplaceAllWith('*').
    /// let word_filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());
    ///
    /// assert_eq!(word_filter.censor("this string contains foo"), "this string contains ***");
    /// ```
    #[must_use]
    pub fn censor(&self, input: &str) -> String {
        let mut output = String::with_capacity(input.len());
        let mut input_char_indices = input.char_indices();
        // Pointers are sorted on both start and end, due to use of NestedContainmentList.
        let mut prev_end = 0;
        for pointer in self.find_pointers(input).iter() {
            // Insert un-censored characters.
            if pointer.start() > prev_end {
                for _ in 0..(pointer.start() - prev_end) {
                    output.push(unsafe {
                        // SAFETY: Each `pointer` within `pointers` is guaranteed to be within the
                        // bounds of `input`. Additionally, since the `pointer`s are ordered by the
                        // ordering provided by the `NestedContainmentList` and are guaranteed by
                        // that same data structure to not include any nested `pointer`s, each
                        // subsequent `pointer` will cover a new set of `input` characters. Thus,
                        // the `unchecked_unwrap()` here is safe, as it will never fail to unwrap a
                        // value.
                        input_char_indices
                            .next()
                            .map(|(_i, c)| c)
                            .unchecked_unwrap()
                    })
                }
            }
            // Censor the covered characters for this pointer.
            let len = pointer.end() - core::cmp::max(pointer.start(), prev_end);
            match self.options.censor_mode {
                CensorMode::ReplaceAllWith(c) => {
                    for _ in 0..len {
                        output.push(c);
                        input_char_indices.next();
                    }
                }
            }

            prev_end = pointer.end();
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

#[cfg(test)]
mod tests {
    use crate::{CensorMode, Options, RepeatedCharacterMatchMode, WordFilter};
    use alloc::{vec, vec::Vec};

    #[test]
    fn find() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn check() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());

        assert!(filter.check("foo"));
        assert!(!filter.check("bar"));
    }

    #[test]
    fn check_only_partial() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());

        assert!(!filter.check("fo"));
    }

    #[test]
    fn censor() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());

        assert_eq!(filter.censor("foo"), "***");
    }

    #[test]
    fn exceptions() {
        let filter = WordFilter::new(
            &["foo"],
            &["afoo", "foob", "cfood"],
            &[],
            &[],
            Options::default(),
        );

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("afoo"), Vec::new().into_boxed_slice());
        assert_eq!(filter.find("foob"), Vec::new().into_boxed_slice());
        assert_eq!(filter.find("cfood"), Vec::new().into_boxed_slice());
    }

    #[test]
    fn exceptions_and_matches() {
        let filter = WordFilter::new(&["foo"], &["foobar"], &[], &[], Options::default());

        assert_eq!(filter.find("foobarfoo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn separators() {
        let filter = WordFilter::new(&["foo"], &[], &[" "], &[], Options::default());

        assert_eq!(filter.find("f oo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn aliases() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[("o", "a")], Options::default());

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fao"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("foa"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("faa"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn aliases_on_aliases() {
        let filter = WordFilter::new(
            &["foo"],
            &[],
            &[],
            &[("o", "a"), ("a", "b")],
            Options::default(),
        );

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fbo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fob"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fbb"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn merged_aliases() {
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[("b", "cd"), ("a", "ef"), ("de", "g")],
            Options::default(),
        );

        assert_eq!(filter.find("cgfr"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn merged_aliases_contiguous() {
        let filter = WordFilter::new(
            &["ahj"],
            &[],
            &[],
            &[("a", "bc"), ("cdef", "g"), ("h", "de"), ("j", "fi")],
            Options::default(),
        );

        assert_eq!(filter.find("bcdefi"), vec!["ahj"].into_boxed_slice());
        assert_eq!(filter.find("bgi"), vec!["ahj"].into_boxed_slice());
    }

    #[test]
    fn merged_aliases_over_full_match() {
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[("b", "x"), ("a", "y"), ("r", "z"), ("xyz", "w")],
            Options::default(),
        );

        assert_eq!(filter.find("w"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn recursive_alias_no_overflow() {
        // Make sure recursive aliases don't cause a stack overflow.
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[("a", "b"), ("b", "a")],
            Options {
                repeated_character_match_mode:
                    RepeatedCharacterMatchMode::DisallowRepeatedCharacters,
                censor_mode: CensorMode::ReplaceAllWith('*'),
            },
        );

        assert_eq!(filter.find("abr"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn alias_after_separator() {
        let filter = WordFilter::new(&["bar"], &[], &[" "], &[("a", "A")], Options::default());

        assert_eq!(filter.find("b Ar"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn options_repeated_characters_allowed() {
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[],
            Options {
                repeated_character_match_mode: RepeatedCharacterMatchMode::AllowRepeatedCharacters,
                censor_mode: CensorMode::ReplaceAllWith('*'),
            },
        );

        assert_eq!(filter.find("bbbaaaarrrr"), vec!["bar"].into_boxed_slice());
        assert_eq!(filter.censor("baaar"), "*****");
    }

    #[test]
    fn options_repeated_characters_disallowed() {
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[],
            Options {
                repeated_character_match_mode:
                    RepeatedCharacterMatchMode::DisallowRepeatedCharacters,
                censor_mode: CensorMode::ReplaceAllWith('*'),
            },
        );

        assert_eq!(filter.find("bbbaaaarrrr"), vec![].into_boxed_slice());
    }

    #[test]
    fn options_censor_mode() {
        let filter = WordFilter::new(
            &["foo"],
            &[],
            &[],
            &[],
            Options {
                repeated_character_match_mode: RepeatedCharacterMatchMode::AllowRepeatedCharacters,
                censor_mode: CensorMode::ReplaceAllWith('#'),
            },
        );

        assert_eq!(filter.censor("foo"), "###");
    }

    #[test]
    fn separator_at_front_and_back_of_match() {
        let word_filter = WordFilter::new(&["foo"], &[], &[" "], &[], Options::default());

        assert_eq!(word_filter.censor("bar foo bar"), "bar *** bar");
    }
}
