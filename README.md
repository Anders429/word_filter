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

A Word Filter is useful for checking and censoring user-generated text in chat applications, online
games, and many other contexts.

## Usage
The most common usage for this crate is to generate a `WordFilter` at compile time using a
[build script](https://doc.rust-lang.org/cargo/reference/build-scripts.html) using the
[`codegen`](https://docs.rs/word_filter/*/word_filter/codegen) module. See the following simple
example and the documentation for further details.

### Example
For example, a simple `WordFilter` can be generated by the following.

First, add the `word_filter` crate to both the `Cargo.toml` `[dependencies]` and
`[build-dependencies]` lists.

``` toml
[dependencies]
word_filter = "0.7.0"

[build-dependencies]
word_filter = "0.7.0"
```

Next, generate the `WordFilter` in the `build.rs` file.

``` rust
use std::{
    env,
    fs::File,
    io::{BufWriter, Write},
    path::Path,
};
use word_filter::codegen::{Visibility, WordFilterGenerator};

fn main() {
    let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    let mut file = BufWriter::new(File::create(&path).unwrap());

    writeln!(
        &mut file,
        "{}",
        WordFilterGenerator::new()
            .visibility(Visibility::Pub)
            .word("foo")
            .generate("FILTER")
        );
}
```

And finally, include the generated code in the `lib.rs` file.

``` rust
include!(concat!(env!("OUT_DIR"), "/codegen.rs"));

assert!(FILTER.censor("Should censor foo."), "Should censor ***.");
```

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
