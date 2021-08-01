//! Macros for creating censors to be used in a [`WordFilter`].
//!
//! These macros are provided for conveniently creating common censor functions. The resulting
//! functions have the signature `fn(&str) -> String` and can therefore be provided when calling
//! the [`censor_with()`] method on a [`WordFilter`].
//!
//! # Example
//! Assuming a compile-time constructed `WordFilter` `FILTER`, defined in a `build.rs` as:
//!
//! ``` ignore
//! use std::{
//!     env,
//!     fs::File,
//!     io::{BufWriter, Write},
//!     path::Path,
//! };
//! use word_filter_codegen::WordFilterGenerator;
//!
//! fn main() {
//!     let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
//!     let mut file = BufWriter::new(File::create(&path).unwrap());
//!
//!     writeln!(
//!         &mut file,
//!         "{}",
//!         WordFilterGenerator::new()
//!             .word("foo")
//!             .generate("FILTER")
//!         );
//! }
//! ```
//!
//! an input can be censored with a custom censor function as follows:
//!
//! ``` ignore
//! use word_filter::censor;
//!
//! include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
//!
//! assert!(
//!     FILTER.censor_with("this string contains foo", censor::replace_graphemes_with("#")),
//!     "this string contains ###"
//! );
//! ```
//!
//! [`WordFilter`]: crate::WordFilter
//! [`censor_with()`]: crate::WordFilter::censor_with

#[doc(hidden)]
pub use alloc::{borrow::ToOwned, string::String};
#[doc(hidden)]
pub use unicode_segmentation::UnicodeSegmentation;

/// Creates a censor replacing every grapheme with the given string.
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
/// use word_filter_codegen::WordFilterGenerator;
///
/// fn main() {
///     let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
///     let mut file = BufWriter::new(File::create(&path).unwrap());
///
///     writeln!(
///         &mut file,
///         "{}",
///         WordFilterGenerator::new()
///             .word("fõõ")
///             .generate("FILTER")
///         );
/// }
/// ```
///
/// a custom censor function can be used as follows:
///
/// ``` ignore
/// include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
///
/// assert!(
///     FILTER.censor_with("this string contains fõõ", censor::replace_graphemes_with("#")),
///     "this string contains ###"
/// );
/// ```
#[macro_export]
macro_rules! _replace_graphemes_with {
    ($s:literal) => {
        |word: &str| {
            use $crate::censor::UnicodeSegmentation;
            word.graphemes(true).fold(
                $crate::censor::String::with_capacity(word.len()),
                |mut accumulator, _cluster| {
                    accumulator.push_str($s);
                    accumulator
                },
            )
        }
    };
}

#[doc(inline)]
pub use _replace_graphemes_with as replace_graphemes_with;

/// Creates a sensor replacing the full matched words with the given string.
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
/// use word_filter_codegen::WordFilterGenerator;
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
/// a custom censor function can be used as follows:
///
/// ``` ignore
/// include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
///
/// assert!(
///     FILTER.censor_with("this string contains foo", censor::replace_words_with("<censored>")),
///     "this string contains <censored>"
/// );
/// ```
#[macro_export]
macro_rules! _replace_words_with {
    ($s:literal) => {
        |_| {
            use $crate::censor::ToOwned;
            $s.to_owned()
        }
    };
}

#[doc(inline)]
pub use _replace_words_with as replace_words_with;

#[cfg(test)]
mod tests {
    use crate::censor::{replace_graphemes_with, replace_words_with};

    #[test]
    fn replace_graphemes() {
        assert_eq!(replace_graphemes_with!("#")("foo"), "###");
        assert_eq!(replace_graphemes_with!("#")("ã"), "#");
    }

    #[test]
    fn replace_words() {
        assert_eq!(replace_words_with!("bar")("foo"), "bar");
    }
}
