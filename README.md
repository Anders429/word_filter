# word_filter

[![GitHub Workflow Status](https://img.shields.io/github/workflow/status/Anders429/word_filter/Tests)](https://github.com/Anders429/word_filter/actions)
[![codecov.io](https://img.shields.io/codecov/c/gh/Anders429/word_filter)](https://codecov.io/gh/Anders429/word_filter)
[![crates.io](https://img.shields.io/crates/v/word_filter)](https://crates.io/crates/word_filter)
[![docs.rs](https://docs.rs/word_filter/badge.svg)](https://docs.rs/word_filter)
[![MSRV](https://img.shields.io/badge/rustc-1.51.0+-yellow.svg)](#minimum-supported-rust-version)
[![License](https://img.shields.io/crates/l/word_filter)](#license)

A Word Filter for filtering text.

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

A Word Filter is useful for checking and altering user-generated text in chat applications, online
games, and many other contexts.

## Usage
An example of a basic Word Filter is as follows:

```rust
use word_filter::WordFilterBuilder;

let filter = WordFilterBuilder::new().words(&["foo", "bar"]).build();

assert_eq!(filter.censor("Should censor foo and bar."), "Should censor *** and ***.");
```

See the documentation for more in-depth usage.

## Minimum Supported Rust Version
This crate is guaranteed to compile on stable `rustc 1.51.0` and up.

## License
This project is licensed under either of

* Apache License, Version 2.0
([LICENSE-APACHE](https://github.com/Anders429/word_filter/blob/HEAD/LICENSE-APACHE) or
http://www.apache.org/licenses/LICENSE-2.0)
* MIT license
([LICENSE-MIT](https://github.com/Anders429/word_filter/blob/HEAD/LICENSE-MIT) or
http://opensource.org/licenses/MIT)

at your option.

### Contribution
Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
