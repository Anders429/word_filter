//! Code generation logic for a state within the push-down automaton.

use crate::pda::{Attributes, Flags};
use alloc::{
    borrow::ToOwned,
    collections::{BTreeMap, BTreeSet},
    format,
    string::String,
    vec::Vec,
};

impl Flags {
    /// Returns the generated definition of this type.
    pub(super) fn to_definition(&self) -> String {
        format!(
            "word_filter::pda::Flags::from_bits_truncate({})",
            self.bits()
        )
    }
}

impl Attributes<'_> {
    fn to_definition(&self) -> String {
        format!(
            "word_filter::pda::Attributes::new(
                {},
                {},
            )",
            self.flags().to_definition(),
            match self.word() {
                Some(word) => format!("Some(\"{}\")", word),
                None => "None".to_owned(),
            }
        )
    }
}

/// Push-down automaton state code generator.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub(super) struct State<'a> {
    pub(super) attributes: Attributes<'a>,
    pub(super) c_transitions: BTreeMap<char, usize>,
    pub(super) aliases: BTreeSet<(usize, usize)>,
    pub(super) graphemes: BTreeSet<usize>,
}

impl State<'_> {
    /// Returns the state's generated definition.
    pub(super) fn to_definition(&self, identifier: &str) -> String {
        format!(
            "        ::word_filter::pda::State {{
            attributes: {},
            c_transitions: {},
            aliases: {},
            graphemes: {},
        }}",
            self.attributes.to_definition(),
            self.define_c_transition_function(identifier),
            self.define_aliases(identifier),
            self.define_graphemes(identifier),
        )
    }

    /// Define the transition function for all direct character transitions.
    fn define_c_transition_function(&self, identifier: &str) -> String {
        format!(
            "|c| {{
                match c {{\n{}
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
            "                    '{}' => Some(&{}.states[{}]),",
            c.escape_default(),
            identifier,
            index
        )
    }

    /// Define the aliases field.
    fn define_aliases(&self, identifier: &str) -> String {
        format!(
            "&[\n{}\n                ]",
            self.aliases
                .iter()
                .map(|(alias, r#return)| self.define_alias(identifier, *alias, *r#return))
                .collect::<Vec<_>>()
                .join(",\n")
        )
    }

    /// Define a single alias entry.
    fn define_alias(&self, identifier: &str, alias: usize, r#return: usize) -> String {
        format!(
            "                    (&{}.states[{}], &{}.states[{}])",
            identifier, alias, identifier, r#return
        )
    }

    /// Define the graphemes field.
    fn define_graphemes(&self, identifier: &str) -> String {
        format!(
            "&[\n{}\n                ]",
            self.graphemes
                .iter()
                .map(|grapheme| self.define_grapheme(identifier, *grapheme))
                .collect::<Vec<_>>()
                .join(",\n")
        )
    }

    /// Define a single grapheme entry.
    fn define_grapheme(&self, identifier: &str, grapheme: usize) -> String {
        format!("                    &{}.states[{}]", identifier, grapheme)
    }
}
