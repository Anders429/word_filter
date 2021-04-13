//! Macros for creating censors to be used in a [`WordFilter`].
//!
//! These macros are provided for conveniently creating common censor functions. The resulting
//! functions have the signature `fn(&str) -> String` and can therefore be provided during building
//! of a `WordFilter`.
//!
//! # Examples
//! Creating a `WordFilter` with a custom censor is done as follows:
//!
//! ```
//! use word_filter::{censor, WordFilterBuilder};
//!
//! let filter = WordFilterBuilder::new().censor(censor::replace_chars_with!("#")).build();
//! ```
//!
//! Note that if the options here do not suite your use case, you can provide a custom function with
//! a closure instead. The following code block has the same effect as the one above:
//!
//! ```
//! use word_filter::WordFilterBuilder;
//!
//! let filter = WordFilterBuilder::new()
//!     .censor(|input| input.chars().fold(String::with_capacity(input.len()), |mut acc, _| {
//!         acc.push('#');
//!         acc
//!     }))
//!     .build();
//! ```
//!
//! This is a bit more verbose, which is why these macros are provided for the most common cases.
//!
//! [`WordFilter`]: crate::WordFilter

#[doc(hidden)]
pub use alloc::string::String;
#[cfg(feature = "unicode-segmentation")]
#[doc(hidden)]
pub use unicode_segmentation::UnicodeSegmentation;

/// Creates a censor replacing every character with the given string.
///
/// # Example
/// ```
/// use word_filter::{censor, WordFilterBuilder};
///
/// let filter = WordFilterBuilder::new()
///     .words(&["foo"])
///     .censor(censor::replace_chars_with!("#"))
///     .build();
///
/// assert_eq!(filter.censor("foo"), "###");
/// ```
#[macro_export]
macro_rules! _replace_chars_with {
    ($s:literal) => {
        |word: &str| {
            word.chars().fold(
                $crate::censor::String::with_capacity(word.len()),
                |mut accumulator, _char| {
                    accumulator.push_str($s);
                    accumulator
                },
            )
        }
    };
}

#[doc(inline)]
pub use _replace_chars_with as replace_chars_with;

/// Creates a censor replacing every grapheme with the given string.
///
/// # Example
/// ```
/// use word_filter::{censor, WordFilterBuilder};
///
/// let filter = WordFilterBuilder::new()
///     .words(&["bãr"])
///     .censor(censor::replace_graphemes_with!("#"))
///     .build();
///
/// assert_eq!(filter.censor("bãr"), "###");
/// ```
#[cfg(feature = "unicode-segmentation")]
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

#[cfg(feature = "unicode-segmentation")]
#[doc(inline)]
pub use _replace_graphemes_with as replace_graphemes_with;

#[cfg(test)]
mod tests {
    use crate::censor::replace_chars_with;
    #[cfg(feature = "unicode-segmentation")]
    use crate::censor::replace_graphemes_with;

    #[test]
    fn replace_chars() {
        assert_eq!(replace_chars_with!("#")("foo"), "###");
        assert_eq!(replace_chars_with!("#")("ã"), "##");
    }

    #[cfg(feature = "unicode-segmentation")]
    #[test]
    fn replace_graphemes() {
        assert_eq!(replace_graphemes_with!("#")("foo"), "###");
        assert_eq!(replace_graphemes_with!("#")("ã"), "#");
    }
}
