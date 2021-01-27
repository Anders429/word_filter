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

// The following clippy allowances are due to the MSRV of this crate being less than the required
// MSRV for each lint. The required MSRV for each lint is listed below. If the MSRV is bumped enough
// to allow usage of a lint, it should be removed from this list.
// NOTE: This will no longer be necessary with the next stable release (1.50.0), as the MSRV
// specification can be placed in a config file at that point..
//
// Required MSRVs:
// - manual_strip: 1.45.0
// - match_like_matches_macro: 1.42.0
#![allow(clippy::manual_strip, clippy::match_like_matches_macro)]
#![no_std]

extern crate alloc;

mod node;
mod pointer;

use alloc::{
    borrow::ToOwned,
    boxed::Box,
    collections::VecDeque,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use core::pin::Pin;
use hashbrown::HashMap;
use nested_containment_list::NestedContainmentList;
use node::Node;
use pointer::{Pointer, PointerStatus};

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
    #[allow(dead_code)]
    alias_map: HashMap<String, Pin<Box<Node<'a>>>>,
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
            alias_map
                .entry((*value).to_string())
                .or_insert_with(|| Box::pin(Node::new()))
                .add_return(alias);
        }
        // Find merged aliases.
        // First, find all aliases that can possibly be combined by a value.
        let mut queue = VecDeque::new();
        for (value, alias) in aliases {
            for (merge_value, _) in aliases {
                let overlap_value = str_overlap::overlap(alias, merge_value);
                if overlap_value.is_empty() || overlap_value == *merge_value {
                    continue;
                }
                queue.push_back((
                    (*value).to_string(),
                    merge_value[overlap_value.len()..].to_string(),
                    (*alias).to_string(),
                ));
            }
        }
        // Now, find aliases that complete the combination.
        let mut new_aliases = Vec::new();
        while let Some((value, target_value, alias)) = queue.pop_front() {
            for (new_value, new_alias) in aliases {
                if target_value == *new_alias || new_alias.starts_with(&target_value) {
                    new_aliases
                        .push((value.to_string() + new_value, alias.to_string() + new_alias));
                } else if target_value.starts_with(new_alias) {
                    // If the combination isn't complete, push it to the queue and try again.
                    queue.push_back((
                        value.to_string() + new_value,
                        target_value[new_alias.len()..].to_string(),
                        alias.to_string() + new_alias,
                    ));
                }
            }
        }
        for (value, alias) in new_aliases {
            alias_map
                .entry(value)
                .or_insert_with(|| Box::pin(Node::new()))
                .add_return(&alias);
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
                    &*(&*alias_map[alias_value] as *const Node)
                };
                alias_map
                    .get_mut(value)
                    .unwrap()
                    .add_alias(alias_value, alias_node);
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
                root.add_alias(value, &*(&**node as *const Node));
            }
        }

        Self {
            root,
            separator_root,
            alias_map,
            options,
        }
    }

    /// Create new `Pointer`s for the aliases at the `pointer`'s `current_node`.
    fn push_aliases(
        &self,
        pointer: &Pointer<'a>,
        new_pointers: &mut Vec<Pointer<'a>>,
        visited: &[&Node],
    ) {
        for (alias_node, return_node) in &pointer.current_node.aliases {
            if visited.iter().any(|n| core::ptr::eq(*n, *alias_node)) {
                continue;
            }
            let mut return_nodes = pointer.return_nodes.clone();
            return_nodes.push(return_node);
            let alias_pointer =
                Pointer::new(alias_node, return_nodes, pointer.start, pointer.len, false);
            let mut new_visited = visited.to_owned();
            new_visited.push(alias_node);
            self.push_aliases(&alias_pointer, new_pointers, &new_visited);
            new_pointers.push(alias_pointer);
        }
    }

    /// Finds all `Pointer`s that encounter matches.
    ///
    /// This also excludes all `Pointer`s that encountered matches but whose ranges also are
    /// contained within ranges are `Pointer`s who encountered exceptions.
    fn find_pointers(&self, input: &str) -> Box<[Pointer]> {
        let root_pointer = Pointer::new(&self.root, Vec::new(), 0, 0, false);
        let mut pointers = Vec::new();
        self.push_aliases(&root_pointer, &mut pointers, &[]);
        pointers.push(root_pointer);
        let mut found = Vec::new();
        for (i, c) in input.chars().enumerate() {
            let mut new_pointers = Vec::new();
            for mut pointer in pointers.drain(..) {
                let mut last_pointer = pointer.clone();
                if pointer.step(c) {
                    // Aliases.
                    self.push_aliases(&pointer, &mut new_pointers, &[]);
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
                } else if let PointerStatus::Match(_) = pointer.status {
                    found.push(pointer);
                } else if let PointerStatus::Exception(_) = pointer.status {
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
                PointerStatus::Match(_) | PointerStatus::Exception(_) => found.push(pointer),
                _ => {}
            }
        }

        // Only return outer-most matched words which aren't part of a longer exception.
        NestedContainmentList::from_slice(&found)
            .sublist()
            .map(|element| element.value)
            .filter_map(|p| {
                if let PointerStatus::Match(_) = p.status {
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
    pub fn find(&self, input: &str) -> Box<[&str]> {
        self.find_pointers(input)
            .iter()
            .map(|pointer| {
                if let PointerStatus::Match(s) = pointer.status {
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
    pub fn censor(&self, input: &str) -> String {
        let mut output = input.to_string();
        for pointer in self.find_pointers(input).iter() {
            let mut new_output = String::with_capacity(output.len());
            let start = pointer.start;
            let end = start + pointer.found_len.unwrap();
            for (i, c) in output.chars().enumerate() {
                if i < start || i > end {
                    new_output.push(c);
                } else {
                    match self.options.censor_mode {
                        CensorMode::ReplaceAllWith(c) => new_output.push(c),
                    }
                }
            }
            output = new_output;
        }
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
