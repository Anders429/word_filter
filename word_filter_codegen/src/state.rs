//! Code generation logic for a state within the push-down automaton.

use crate::r#type::Type;
use alloc::{
    borrow::ToOwned,
    collections::{BTreeMap, BTreeSet},
    format,
    string::String,
    vec::Vec,
};

/// Push-down automaton state code generator.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) struct State<'a> {
    pub(crate) r#type: Type<'a>,
    pub(crate) c_transitions: BTreeMap<char, usize>,
    pub(crate) into_separator: bool,
    pub(crate) repetition: Option<usize>,
    pub(crate) into_repetition: bool,
    pub(crate) take_repetition: bool,
    pub(crate) aliases: BTreeSet<(usize, usize)>,
    pub(crate) graphemes: BTreeSet<usize>,
}

impl State<'_> {
    /// Returns the state's generated definition.
    pub(crate) fn to_definition(&self, identifier: &str) -> String {
        format!(
            "::word_filter::pda::State {{
                r#type: {},
                c_transitions: {},
                into_separator: {},
                repetition: {},
                into_repetition: {},
                take_repetition: {},
                aliases: {},
                graphemes: {},
            }}",
            self.r#type.to_definition(),
            self.define_c_transition_function(identifier),
            self.into_separator,
            self.define_repetition(identifier),
            self.into_repetition,
            self.take_repetition,
            self.define_aliases(identifier),
            self.define_graphemes(identifier),
        )
    }

    /// Define the transition function for all direct character transitions.
    fn define_c_transition_function(&self, identifier: &str) -> String {
        format!(
            "|c| {{
                match c {{
                    {}
                    _ => None,
                }}
            }}",
            self.c_transitions
                .iter()
                .map(|(c, index)| self.define_c_transition(identifier, *c, *index))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }

    /// Define the transition statement for a singe character transition.
    fn define_c_transition(&self, identifier: &str, c: char, index: usize) -> String {
        format!(
            "'{}' => Some(&{}.states[{}]),",
            c.escape_default(),
            identifier,
            index
        )
    }

    /// Define the repetition transition field.
    fn define_repetition(&self, identifier: &str) -> String {
        match self.repetition {
            Some(index) => format!("Some(&{}.states[{}])", identifier, index),
            None => "None".to_owned(),
        }
    }

    /// Define the aliases field.
    fn define_aliases(&self, identifier: &str) -> String {
        format!(
            "&[{}]",
            self.aliases
                .iter()
                .map(|(alias, r#return)| self.define_alias(identifier, *alias, *r#return))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    /// Define a single alias entry.
    fn define_alias(&self, identifier: &str, alias: usize, r#return: usize) -> String {
        format!(
            "(&{}.states[{}], &{}.states[{}])",
            identifier, alias, identifier, r#return
        )
    }

    /// Define the graphemes field.
    fn define_graphemes(&self, identifier: &str) -> String {
        format!(
            "&[{}]",
            self.graphemes
                .iter()
                .map(|grapheme| self.define_grapheme(identifier, *grapheme))
                .collect::<Vec<_>>()
                .join(",")
        )
    }

    /// Define a single grapheme entry.
    fn define_grapheme(&self, identifier: &str, grapheme: usize) -> String {
        format!("&{}.states[{}]", identifier, grapheme)
    }
}
