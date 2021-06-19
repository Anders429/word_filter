//! Code generation for the [`word_filter`](https://docs.rs/word_filter) crate.
//!
//! This crate is intended to be used alongside the `word_filter` crate to generate code at compile
//! time. To use, add `word_filter_codegen` to the `[build-dependency]` list and generate the code
//! in a `build.rs` file. Then [`include!`] the file in `lib.rs`.
//!
//! # Example
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
//! ``` no_run
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
//!
//! [`WordFilter`]: https://docs.rs/word_filter/0.6.0/struct.WordFilter.html

#![no_std]

extern crate alloc;

mod pda;
mod state;
mod r#type;

use alloc::{
    borrow::ToOwned,
    collections::{BTreeSet, VecDeque},
    format,
    string::{String, ToString},
    vec::Vec,
};
use pda::Pda;
use str_overlap::Overlap;

/// Visibility of generated code.
///
/// Can be provided to [`WordFilterGenerator`] to define the visibility of the resulting code.
///
/// # Example
/// The following code example generates a [`WordFilter`] that is visible to the rest of the crate:
///
/// ```
/// use word_filter_codegen::{Visibility, WordFilterGenerator};
///
/// let generated_code = WordFilterGenerator::new()
///     .visibility(Visibility::PubCrate)
///     .word("foo")
///     .generate("FILTER");
/// ```
///
/// [`WordFilter`]: https://docs.rs/word_filter/0.6.0/struct.WordFilter.html
#[derive(Clone, Debug)]
pub enum Visibility {
    Private,
    Pub,
    PubCrate,
    PubIn(String),
}

impl Default for Visibility {
    fn default() -> Self {
        Self::Private
    }
}

impl ToString for Visibility {
    fn to_string(&self) -> String {
        match self {
            Visibility::Private => String::new(),
            Visibility::Pub => "pub".to_owned(),
            Visibility::PubCrate => "pub(crate)".to_owned(),
            Visibility::PubIn(path) => format!("pub(in {})", path),
        }
    }
}

/// Code generator for [`WordFilter`]s, following the builder pattern.
///
/// Generates code that can be compiled to a `WordFilter`. Filtered **words**, ignored
/// **exceptions**, allowed **separators**, and character **aliases** may all be provided through
/// the associated methods.
///
/// # Example
/// ```
/// use word_filter_codegen::{Visibility, WordFilterGenerator};
///
/// let generated_code = WordFilterGenerator::new()
///     .visibility(Visibility::Pub)
///     .word("foo")
///     .exception("foobar")
///     .separator(' ')
///     .alias('f', 'F')
///     .generate("FILTER");
/// ```
///
/// The generated code can then be written to a file in the `OUT_DIR`. See crate-level
/// documentation for more details.
///
/// [`WordFilter`]: https://docs.rs/word_filter/0.6.0/struct.WordFilter.html
#[derive(Clone, Debug, Default)]
pub struct WordFilterGenerator {
    words: Vec<String>,
    exceptions: Vec<String>,
    separators: Vec<String>,
    aliases: Vec<(String, String)>,
    visibility: Visibility,
    doc: String,
}

impl WordFilterGenerator {
    /// Creates a new WordFilterGenerator.
    ///
    /// This is equivalent to `WordFilterGenerator::default()`.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let generator = WordFilterGenerator::new();
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a single word.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.word("foo");
    /// ```
    #[inline]
    pub fn word<S>(&mut self, word: S) -> &mut Self
    where
        S: ToString,
    {
        self.words.push(word.to_string());
        self
    }

    /// Add words.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.words(&["foo", "bar"]);
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

    /// Add a single exception.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.exception("foo");
    /// ```
    #[inline]
    pub fn exception<S>(&mut self, exception: S) -> &mut Self
    where
        S: ToString,
    {
        self.exceptions.push(exception.to_string());
        self
    }

    /// Add exceptions.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.exceptions(&["foo", "bar"]);
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

    /// Add a single separator.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.separator("foo");
    /// ```
    #[inline]
    pub fn separator<S>(&mut self, separator: S) -> &mut Self
    where
        S: ToString,
    {
        self.separators.push(separator.to_string());
        self
    }

    /// Add separators.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.separators(&["foo", "bar"]);
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

    /// Add a single alias.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.alias("foo", "bar");
    /// ```
    #[inline]
    pub fn alias<S, T>(&mut self, source: S, alias: T) -> &mut Self
    where
        S: ToString,
        T: ToString,
    {
        self.aliases.push((source.to_string(), alias.to_string()));
        self
    }

    /// Add aliases.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.aliases(&[("foo", "bar"), ("baz", "qux")]);
    /// ```
    #[inline]
    pub fn aliases<'a, I, S, T>(&mut self, aliases: I) -> &mut Self
    where
        I: IntoIterator<Item = &'a (S, T)>,
        S: ToString + 'a,
        T: ToString + 'a,
    {
        self.aliases.extend(
            aliases
                .into_iter()
                .map(|(s, t)| (s.to_string(), t.to_string())),
        );
        self
    }

    /// Set visibility of the generated code.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::{Visibility, WordFilterGenerator};
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.visibility(Visibility::Pub);
    /// ```
    #[inline]
    pub fn visibility(&mut self, visibility: Visibility) -> &mut Self {
        self.visibility = visibility;
        self
    }

    /// Set the doc string of the generated code.
    ///
    /// The generated code will be generated with `doc` as the item-level doc-string.
    ///
    /// # Example
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.doc("foo");
    /// ```
    ///
    /// ## Multiple Lines
    /// For doc strings that contain multiple lines, users are advised to use the
    /// [`indoc`](https://crates.io/crates/indoc) crate.
    ///
    /// ```
    /// use word_filter_codegen::WordFilterGenerator;
    /// use indoc::indoc;
    ///
    /// let mut generator = WordFilterGenerator::new();
    /// generator.doc(indoc!(
    ///    "foo
    ///
    ///     bar baz quux"
    /// ));
    /// ```
    #[inline]
    pub fn doc<S>(&mut self, doc: S) -> &mut Self
    where
        S: ToString,
    {
        self.doc = doc.to_string();
        self
    }

    /// Generate code defining a [`WordFilter`] with the given words, exceptions, separators,
    /// aliases, and visibility.
    ///
    /// The generated code is most often written to a file at compile time within a `build.rs`
    /// script. An example `build.rs` is as follows:
    ///
    /// ``` no_run
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
    ///             .visibility(Visibility::Pub)
    ///             .word("foo")
    ///             .generate("FILTER")
    ///         );
    /// }
    /// ```
    ///
    /// [`WordFilter`]: https://docs.rs/word_filter/0.6.0/struct.WordFilter.html
    pub fn generate(&self, identifier: &str) -> String {
        let mut pda = Pda::new();

        for word in &self.words {
            pda.add_word(word);
        }
        for exception in &self.exceptions {
            pda.add_exception(exception);
        }
        for separator in &self.separators {
            pda.add_separator(separator);
        }

        let mut aliases = self.aliases.clone();
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
        while let Some((value, target_value, alias)) = queue.pop_front() {
            for (new_value, new_alias) in &self.aliases {
                if target_value == *new_alias || new_alias.starts_with(&target_value) {
                    aliases.push((value.clone() + new_value, alias.clone() + new_alias));
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
        let mut alias_indices = Vec::new();
        for (value, alias) in aliases {
            alias_indices.push((value, pda.initialize_alias(&alias)));
        }

        // Apply aliases on each other.
        for (value, index) in &alias_indices {
            for (alias_value, alias_index) in &alias_indices {
                if value == alias_value {
                    continue;
                }
                pda.add_alias(alias_value, *alias_index, *index, &mut BTreeSet::new());
            }
        }

        // Apply aliases on root.
        for (value, index) in alias_indices {
            pda.add_alias(&value, index, 0, &mut BTreeSet::new());
        }

        pda.minimize();

        format!(
            "#[doc = \"{}\"]
            {} static {}: {} = {};",
            self.doc,
            self.visibility.to_string(),
            identifier,
            pda.to_type(),
            pda.to_definition(identifier)
        )
    }
}
