//! Code generation logic for the push-down automaton structure that makes up a `WordFilter`.

use crate::{r#type::Type, state::State};
use alloc::{collections::BTreeSet, format, string::String, vec, vec::Vec};
use debug_unreachable::debug_unreachable;
use unicode_segmentation::UnicodeSegmentation;

// Reserved indices.
const ENTRY_INDEX: usize = 0;
const SEPARATOR_INDEX: usize = 1;
const SEPARATOR_RETURN_INDEX: usize = 2;

/// Push-down automaton code generator.
///
/// Contains the logic for both constructing the word filter push-down automaton and generating a
/// resulting `WordFilter`.
#[derive(Debug)]
pub(crate) struct Pda<'a> {
    states: Vec<State<'a>>,
}

impl<'a> Pda<'a> {
    /// Create a new push-down automaton code generator.
    pub(crate) fn new() -> Self {
        let mut separator_return = State::default();
        separator_return.r#type = Type::SeparatorReturn;
        Self {
            states: vec![State::default(), State::default(), separator_return],
        }
    }

    /// Add a path along input `s`, ending with state of the specified type.
    fn add_path(&mut self, s: &str, r#type: Type<'a>, index: usize) {
        let mut graphemes = s.graphemes(true);
        let grapheme = match graphemes.next() {
            Some(g) => g,
            None => {
                let mut state = &mut self.states[index];
                if matches!(state.r#type, Type::None) {
                    state.r#type = r#type;
                }
                return;
            }
        };
        if grapheme.chars().count() > 1 {
            let new_index = self.states.len();
            self.states.push(State::default());
            self.states[index].graphemes.insert(new_index);
            self.add_grapheme(grapheme, graphemes.as_str(), r#type, new_index);
        } else {
            let mut chars = s.chars();
            let c = match chars.next() {
                Some(c) => c,
                None => unsafe {
                    // SAFETY: We saw above that a grapheme was found, which means `s` is not
                    // empty.
                    debug_unreachable!()
                },
            };
            let new_index = match self.states[index].c_transitions.get(&c) {
                Some(new_index) => *new_index,
                None => {
                    let new_index = self.states.len();
                    self.states.push(State::default());
                    // Add new state.
                    self.states[index].c_transitions.insert(c, new_index);
                    // Add repeated transition to new state.
                    self.states[new_index].repetition = Some((c, new_index));
                    // Add separator transition to new state.
                    self.states[new_index].into_separator = true;
                    new_index
                }
            };

            self.add_path(chars.as_str(), r#type, new_index)
        }
    }

    /// Add grapheme states along input `g`.
    ///
    /// Following the grapheme path, a regular path will be added using input `s`.
    fn add_grapheme(&mut self, g: &str, s: &str, r#type: Type<'a>, index: usize) {
        let mut chars = g.chars();
        let c = match chars.next() {
            Some(c) => c,
            None => return,
        };
        let new_index = self.states.len();
        self.states.push(State::default());
        self.states[index].c_transitions.insert(c, new_index);
        self.add_grapheme_with_return(chars.as_str(), s, r#type, new_index, new_index, c)
    }

    /// Add a grapheme path, ending with a repetition to `return_index`.
    fn add_grapheme_with_return(
        &mut self,
        g: &str,
        s: &str,
        r#type: Type<'a>,
        index: usize,
        return_index: usize,
        return_c: char,
    ) {
        let mut chars = g.chars();
        let c = match chars.next() {
            Some(c) => c,
            None => return,
        };
        let remaining_g = chars.as_str();
        let new_index = self.states.len();
        self.states.push(State::default());
        self.states[index].c_transitions.insert(c, new_index);
        if remaining_g.is_empty() {
            // Repeating transition.
            self.states[new_index].repetition = Some((return_c, return_index));
            // Separator.
            self.states[new_index].into_separator = true;
            // Continue down normal path.
            self.add_path(s, r#type, new_index);
        } else {
            self.add_grapheme_with_return(
                remaining_g,
                s,
                r#type,
                new_index,
                return_index,
                return_c,
            );
        }
    }

    /// Add a word.
    #[inline]
    pub(crate) fn add_word(&mut self, s: &'a str) {
        self.add_path(s, Type::Word(s), ENTRY_INDEX)
    }

    /// Add an exception.
    #[inline]
    pub(crate) fn add_exception(&mut self, s: &str) {
        self.add_path(s, Type::Exception, ENTRY_INDEX)
    }

    /// Add separator states using input `s`.
    fn add_separator_internal(&mut self, s: &str, index: usize) {
        let mut chars = s.chars();
        let c = match chars.next() {
            Some(c) => c,
            None => {
                return;
            }
        };
        let remaining_s = chars.as_str();
        let new_index = match (
            remaining_s.is_empty(),
            self.states[index].c_transitions.get(&c),
        ) {
            (true, _) => {
                self.states[index]
                    .c_transitions
                    .insert(c, SEPARATOR_RETURN_INDEX);
                SEPARATOR_RETURN_INDEX
            }
            (_, Some(new_index)) => *new_index,
            _ => {
                let new_index = self.states.len();
                self.states.push(State::default());
                self.states[index].c_transitions.insert(c, new_index);
                new_index
            }
        };
        self.add_separator_internal(remaining_s, new_index)
    }

    /// Add a separator.
    #[inline]
    pub(crate) fn add_separator(&mut self, s: &str) {
        self.add_separator_internal(s, SEPARATOR_INDEX)
    }

    /// Create a new alias, returning the index of the alias's entry state.
    pub(crate) fn initialize_alias(&mut self, s: &str) -> usize {
        let new_index = self.states.len();
        self.states.push(State::default());
        self.add_path(s, Type::Return, new_index);
        new_index
    }

    /// Find the return states for defining an alias along the input `s`.
    fn find_alias_return_states(&self, s: &str, index: usize) -> impl Iterator<Item = usize> {
        let mut return_states = Vec::new();

        let mut chars = s.chars();
        let c = match chars.next() {
            Some(c) => c,
            None => return return_states.into_iter(),
        };
        let remaining_s = chars.as_str();
        self.states[index]
            .c_transitions
            .get(&c)
            .into_iter()
            .for_each(|next_index| {
                if remaining_s.is_empty() {
                    return_states.push(*next_index);
                } else {
                    return_states.extend(self.find_alias_return_states(remaining_s, *next_index));
                }
            });
        self.states[index]
            .graphemes
            .iter()
            .for_each(|grapheme_index| {
                return_states.extend(self.find_alias_return_states(s, *grapheme_index));
            });

        return_states.into_iter()
    }

    /// Apply alias in every possible place along the main path of the push-down automaton.
    pub(crate) fn add_alias(
        &mut self,
        s: &str,
        alias_index: usize,
        current_index: usize,
        visited: &mut BTreeSet<usize>,
    ) {
        // Head recursion.
        for (_c, index) in &self.states[current_index].c_transitions.clone() {
            if !visited.contains(index) {
                visited.insert(*index);
                self.add_alias(s, alias_index, *index, visited);
                visited.remove(index);
            }
        }
        for index in &self.states[current_index].graphemes.clone() {
            if !visited.contains(index) {
                visited.insert(*index);
                self.add_alias(s, alias_index, *index, visited);
                visited.remove(index);
            }
        }
        // Repetitions aren't traversed here because they have always already been visited.

        for return_index in self.find_alias_return_states(s, current_index) {
            self.states[current_index]
                .aliases
                .insert((alias_index, return_index));
        }
    }

    /// Returns the generated `WordFilter`'s type.
    pub(crate) fn to_type(&self) -> String {
        format!("::word_filter::WordFilter<{}>", self.states.len())
    }

    /// Returns the generated `WordFilter`'s definition.
    pub(crate) fn to_definition(&self, identifier: &str) -> String {
        format!(
            "::word_filter::WordFilter {{
            states: [{}],
        }}",
            self.states
                .iter()
                .map(|state| state.to_definition(identifier))
                .collect::<Vec<_>>()
                .join(",")
        )
    }
}
