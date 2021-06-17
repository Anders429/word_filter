//! Code generation logic for the type of a state in the push-down automaton.

use alloc::{borrow::ToOwned, format, string::String};

/// Code generator for a state's type.
#[derive(Debug)]
pub(crate) enum Type<'a> {
    None,
    Word(&'a str),
    Exception,
    Separator,
    Return,
    SeparatorReturn,
}

impl Type<'_> {
    /// Returns the generated definition of this type.
    pub(crate) fn to_definition(&self) -> String {
        match self {
            Type::None => "::word_filter::pda::Type::None".to_owned(),
            Type::Word(s) => format!("::word_filter::pda::Type::Word(\"{}\")", s),
            Type::Exception => "::word_filter::pda::Type::Exception".to_owned(),
            Type::Separator => "::word_filter::pda::Type::Separator".to_owned(),
            Type::Return => "::word_filter::pda::Type::Return".to_owned(),
            Type::SeparatorReturn => "::word_filter::pda::Type::SeparatorReturn".to_owned(),
        }
    }
}

impl Default for Type<'_> {
    #[inline]
    fn default() -> Self {
        Self::None
    }
}
