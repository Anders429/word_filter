# word_filter

[![GitHub Workflow Status](https://img.shields.io/github/workflow/status/Anders429/word_filter/Tests)](https://github.com/Anders429/word_filter/actions)
[![codecov.io](https://img.shields.io/codecov/c/gh/Anders429/word_filter)](https://codecov.io/gh/Anders429/word_filter)
[![crates.io](https://img.shields.io/crates/v/word_filter)](https://crates.io/crates/word_filter)
[![docs.rs](https://docs.rs/word_filter/badge.svg)](https://docs.rs/word_filter)
[![MSRV](https://img.shields.io/badge/rustc-1.36.0+-yellow.svg)](#minimum-supported-rust-version)
![License](https://img.shields.io/crates/l/word_filter)

A robust implementation of a Word Filter.

A Word Filter is a system for identifying and censoring specific words or phrases in strings. Common
usage includes censoring vulgar or profane language and preventing spam or vandelism in 
user-provided content.

The Word Filter implementation provided here allows for advanced filtering functionality, including:
- Finding and censoring filtered words.
- Ignoring words that are considered "exceptions".
- Allowing specification of "aliases", i.e. strings that can replace other strings (for example, an
alias could be created to replace the letter "a" with the character "@").
- Ignoring specified separators (such as spaces or other characters) between letters of filtered
words.

A Word Filter is useful for screening user-generated text in chat applications, online games, and
many other contexts.

## Usage
An example of a functional Word Filter using this crate is as follows:

```rust
use word_filter::{Options, WordFilter};

// Filtered words are words that should be detected by the WordFilter.
let filtered_words = &["foo"];
// Exceptions are words that should not be detected by the WordFilter, even if words inside them 
// are.
let exceptions = &["foobar"];
// Separators are characters that can appear between letters within filtered words.
let separators = &[" ", "_"];
// Aliases define characters that can be found in place of other characters in a match.
let aliases = &[("f", "F")];

// All of these together are used to create a WordFilter.
let word_filter = WordFilter::new(
    filtered_words,
    exceptions,
    separators,
    aliases,
    Options::default(),
);

// The word filter will both identify and censor the word "foo".
assert!(word_filter.check("Should censor foo"));
assert_eq!(word_filter.censor("Should censor foo"), "Should censor ***");

// The word filter does not identify or censor the word "foobar".
assert!(!word_filter.check("Should not censor foobar"));
assert_eq!(word_filter.censor("Should not censor foobar"), "Should not censor foobar");

// The word filter will ignore separators while matching.
assert!(word_filter.check("Should censor f o_o"));
assert_eq!(word_filter.censor("Should censor f o_o"), "Should censor *****");

// The word filter checks for aliases while matching.
assert!(word_filter.check("Should censor Foo"));
assert_eq!(word_filter.censor("Should censor Foo"), "Should censor ***");
```

See the documentation for more in-depth usage.

## Minimum Supported Rust Version
This crate is guaranteed to compile on stable `rustc 1.36.0` and up.
