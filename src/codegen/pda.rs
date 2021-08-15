//! Code generation logic for the push-down automaton structure that makes up a `WordFilter`.

use super::state::State;
use crate::{
    constants::{EXCEPTION_INDEX, SEPARATOR_INDEX, WORD_INDEX},
    pda::{Attributes, Flags},
};
use alloc::{collections::BTreeSet, format, string::String, vec, vec::Vec};
use debug_unreachable::debug_unreachable;
use hashbrown::HashMap;
use unicode_segmentation::UnicodeSegmentation;

/// Create `Attributes` to be passed as `state_attributes` to `add_path()`.
fn create_state_attributes<'a>(
    into_separator: bool,
    into_repetition: bool,
    is_separator: bool,
) -> Attributes<'a> {
    Attributes::new(
        if into_separator {
            Flags::INTO_SEPARATOR
        } else {
            Flags::empty()
        } | if into_repetition {
            Flags::INTO_REPETITION | Flags::TAKE_REPETITION
        } else {
            Flags::empty()
        } | if is_separator {
            Flags::SEPARATOR
        } else {
            Flags::empty()
        },
        None,
    )
}

/// Push-down automaton code generator.
///
/// Contains the logic for both constructing the word filter push-down automaton and generating a
/// resulting `WordFilter`.
#[derive(Debug)]
pub(super) struct Pda<'a> {
    states: Vec<State<'a>>,
}

impl<'a> Pda<'a> {
    /// Create a new push-down automaton code generator.
    pub(super) fn new(
        word_into_repetition: bool,
        exception_into_repetition: bool,
        separator_into_repetition: bool,
    ) -> Self {
        Self {
            states: vec![
                // Word entry state.
                State {
                    attributes: Attributes::new(
                        if word_into_repetition {
                            Flags::INTO_REPETITION
                        } else {
                            Flags::empty()
                        },
                        None,
                    ),
                    ..Default::default()
                },
                // Exception entry state.
                State {
                    attributes: Attributes::new(
                        if exception_into_repetition {
                            Flags::INTO_REPETITION
                        } else {
                            Flags::empty()
                        },
                        None,
                    ),
                    ..Default::default()
                },
                // Separator entry state.
                State {
                    attributes: Attributes::new(
                        if separator_into_repetition {
                            Flags::SEPARATOR | Flags::INTO_REPETITION
                        } else {
                            Flags::SEPARATOR
                        },
                        None,
                    ),
                    ..Default::default()
                },
            ],
        }
    }

    /// Add a path along input `s`, ending with state of the specified type.
    fn add_path(
        &mut self,
        s: &str,
        state_attributes: Attributes<'a>,
        final_attributes: Attributes<'a>,
        index: usize,
    ) {
        let mut graphemes = s.graphemes(true);
        let grapheme = match graphemes.next() {
            Some(g) => g,
            None => {
                self.states[index].attributes.merge(final_attributes);
                return;
            }
        };
        if grapheme.chars().count() > 1 {
            let new_index = self.states.len();
            self.states.push(State::default());
            self.states[index].graphemes.insert(new_index);
            let mut new_attributes = state_attributes.clone();
            new_attributes.remove_take_repetition();
            new_attributes.remove_into_separator();
            self.states[new_index].attributes = new_attributes;
            self.add_grapheme(
                grapheme,
                graphemes.as_str(),
                state_attributes,
                final_attributes,
                new_index,
            );
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
                    self.states[new_index].attributes = state_attributes.clone();
                    new_index
                }
            };

            self.add_path(
                chars.as_str(),
                state_attributes,
                final_attributes,
                new_index,
            )
        }
    }

    /// Add grapheme states along input `g`.
    ///
    /// Following the grapheme path, a regular path will be added using input `s`.
    fn add_grapheme(
        &mut self,
        g: &str,
        s: &str,
        state_attributes: Attributes<'a>,
        final_attributes: Attributes<'a>,
        index: usize,
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
        let mut new_attributes = state_attributes.clone();
        new_attributes.remove_into_repetition();
        if remaining_g.is_empty() {
            self.states[new_index].attributes = new_attributes;
            // Continue down normal path.
            self.add_path(s, state_attributes, final_attributes, new_index);
        } else {
            new_attributes.remove_take_repetition();
            new_attributes.remove_into_separator();
            self.states[new_index].attributes = new_attributes;
            self.add_grapheme(
                remaining_g,
                s,
                state_attributes,
                final_attributes,
                new_index,
            );
        }
    }

    /// Add a word.
    #[inline]
    pub(super) fn add_word(&mut self, s: &'a str, into_separator: bool, into_repetition: bool) {
        self.add_path(
            s,
            create_state_attributes(into_separator, into_repetition, false),
            Attributes::new(Flags::WORD, Some(s)),
            WORD_INDEX,
        )
    }

    /// Add an exception.
    #[inline]
    pub(super) fn add_exception(&mut self, s: &str, into_separator: bool, into_repetition: bool) {
        self.add_path(
            s,
            create_state_attributes(into_separator, into_repetition, false),
            Attributes::new(Flags::EXCEPTION, None),
            EXCEPTION_INDEX,
        )
    }

    /// Add a separator.
    #[inline]
    pub(super) fn add_separator(&mut self, s: &str, into_repetition: bool) {
        self.add_path(
            s,
            create_state_attributes(
                false,
                if s.graphemes(true).count() > 1 {
                    into_repetition
                } else {
                    false
                },
                true,
            ),
            Attributes::new(Flags::SEPARATOR | Flags::RETURN, None),
            SEPARATOR_INDEX,
        )
    }

    /// Create a new alias, returning the index of the alias's entry state.
    fn initialize_alias(&mut self) -> usize {
        let new_index = self.states.len();
        self.states.push(State::default());
        self.states[new_index].attributes = Attributes::new(Flags::INTO_REPETITION, None);
        new_index
    }

    /// Add a return.
    fn add_return(&mut self, index: usize, s: &str, into_separator: bool, into_repetition: bool) {
        self.add_path(
            s,
            create_state_attributes(into_separator, into_repetition, false),
            Attributes::new(Flags::RETURN, None),
            index,
        )
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
    fn add_alias(
        &mut self,
        s: &str,
        alias_index: usize,
        current_index: usize,
        visited: &mut BTreeSet<usize>,
    ) {
        // Head recursion.
        for index in self.states[current_index].c_transitions.clone().values() {
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

    /// Apply aliases at the `root_index`.
    pub(super) fn apply_aliases(
        &mut self,
        aliases: &[(String, String)],
        into_separator: bool,
        into_repetition: bool,
        root_index: usize,
    ) {
        let mut alias_indices = HashMap::new();
        for (value, alias) in aliases {
            let index = alias_indices
                .entry(value)
                .or_insert(self.initialize_alias());
            self.add_return(*index, alias, into_separator, into_repetition);
        }
        // Apply aliases on each other.
        for (value, index) in &alias_indices {
            for (alias_value, alias_index) in &alias_indices {
                if value == alias_value {
                    continue;
                }
                self.add_alias(alias_value, *alias_index, *index, &mut BTreeSet::new());
            }
        }
        // Apply aliases on root.
        for (value, index) in alias_indices {
            self.add_alias(value, index, root_index, &mut BTreeSet::new());
        }
    }

    /// Minimize the push-down automaton.
    ///
    /// Combines states that have the exact same fields. This significantly reduces the size of
    /// larger automaton, but at the const of longer compile time. The algorithm is pretty naive,
    /// just looping through the states repeatedly until it no longer finds states that can be
    /// combined.
    pub(super) fn minimize(&mut self) {
        loop {
            // Find the set of all distinct and duplicated states. The distinct states will be
            // kept.
            let mut distinct_states = HashMap::new();
            // Note that deleted_states will always be ordered from least to greatest.
            let mut deleted_states = Vec::new();
            // Skip the reserved indices during merging.
            for (index, state) in self.states.iter().cloned().enumerate().skip(3) {
                if let Some(canonical_index) = distinct_states.get(&state) {
                    deleted_states.push((index, *canonical_index));
                } else {
                    distinct_states.insert(state, index);
                }
            }
            if deleted_states.is_empty() {
                break;
            }
            let mut new_states = Vec::new();
            // Delete states.
            'state_loop: for (index, mut state) in self.states.drain(..).enumerate() {
                for (deleted_index, replacement_index) in &deleted_states {
                    // Skip if this state is being deleted.
                    if index == *deleted_index {
                        continue 'state_loop;
                    }
                    for transition_index in state.c_transitions.values_mut() {
                        if *transition_index == *deleted_index {
                            *transition_index = *replacement_index;
                        }
                    }
                    let mut new_aliases = BTreeSet::new();
                    for (alias_index, return_index) in state.aliases {
                        let mut new_alias_index = alias_index;
                        let mut new_return_index = return_index;
                        if alias_index == *deleted_index {
                            new_alias_index = *replacement_index;
                        }
                        if return_index == *deleted_index {
                            new_return_index = *replacement_index;
                        }
                        new_aliases.insert((new_alias_index, new_return_index));
                    }
                    state.aliases = new_aliases;
                    let mut new_graphemes = BTreeSet::new();
                    for grapheme_index in state.graphemes {
                        let mut new_grapheme_index = grapheme_index;
                        if grapheme_index == *deleted_index {
                            new_grapheme_index = *replacement_index;
                        }
                        new_graphemes.insert(new_grapheme_index);
                    }
                    state.graphemes = new_graphemes;
                }

                new_states.push(state);
            }

            // Alter states' indices to acount for deletions.
            for mut state in new_states.iter_mut() {
                for (deleted_index, _) in deleted_states.iter().rev() {
                    for transition_index in state.c_transitions.values_mut() {
                        if *transition_index > *deleted_index {
                            *transition_index -= 1;
                        }
                    }
                    let mut new_aliases = BTreeSet::new();
                    for (alias_index, return_index) in &state.aliases {
                        let mut new_alias_index = *alias_index;
                        let mut new_return_index = *return_index;
                        if *alias_index > *deleted_index {
                            new_alias_index -= 1;
                        }
                        if *return_index > *deleted_index {
                            new_return_index -= 1;
                        }
                        new_aliases.insert((new_alias_index, new_return_index));
                    }
                    state.aliases = new_aliases;
                    let mut new_graphemes = BTreeSet::new();
                    for grapheme_index in &state.graphemes {
                        let mut new_grapheme_index = *grapheme_index;
                        if *grapheme_index > *deleted_index {
                            new_grapheme_index -= 1;
                        }
                        new_graphemes.insert(new_grapheme_index);
                    }
                    state.graphemes = new_graphemes;
                }
            }

            self.states = new_states;
        }
    }

    /// Returns the generated `WordFilter`'s type.
    pub(super) fn to_type(&self) -> String {
        format!("::word_filter::WordFilter<{}>", self.states.len())
    }

    /// Returns the generated `WordFilter`'s definition.
    pub(super) fn to_definition(&self, identifier: &str) -> String {
        format!(
            "::word_filter::WordFilter {{\n    states: [\n{}\n    ],\n}}",
            self.states
                .iter()
                .map(|state| state.to_definition(identifier))
                .collect::<Vec<_>>()
                .join(",\n")
        )
    }
}
