//! Code generation logic for the push-down automaton structure that makes up a `WordFilter`.

use crate::{r#type::Type, state::State};
use alloc::{collections::BTreeSet, format, string::String, vec, vec::Vec};
use debug_unreachable::debug_unreachable;
use hashbrown::HashMap;
use unicode_segmentation::UnicodeSegmentation;

// Reserved indices.
const ENTRY_INDEX: usize = 0;
const SEPARATOR_INDEX: usize = 1;

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
        Self {
            states: vec![
                State {
                    into_repetition: true,
                    ..Default::default()
                },
                State {
                    r#type: Type::Separator,
                    ..Default::default()
                },
            ],
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
            self.states[new_index].into_repetition = true;
            self.add_grapheme(grapheme, graphemes.as_str(), r#type, new_index, new_index);
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
                    // Add repetition
                    self.states[new_index].into_repetition = true;
                    self.states[new_index].take_repetition = true;
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
    fn add_grapheme(
        &mut self,
        g: &str,
        s: &str,
        r#type: Type<'a>,
        index: usize,
        return_index: usize,
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
            // Make grapheme transition to repetition.
            self.states[new_index].take_repetition = true;
            // Separator.
            self.states[new_index].into_separator = true;
            // Continue down normal path.
            self.add_path(s, r#type, new_index);
        } else {
            self.add_grapheme(remaining_g, s, r#type, new_index, return_index);
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
                self.states[index].r#type = Type::SeparatorReturn;
                return;
            }
        };
        let new_index = match self.states[index].c_transitions.get(&c) {
            Some(new_index) => *new_index,
            None => {
                let new_index = self.states.len();
                self.states.push(State {
                    r#type: Type::Separator,
                    ..Default::default()
                });
                self.states[index].c_transitions.insert(c, new_index);
                new_index
            }
        };
        self.add_separator_internal(chars.as_str(), new_index)
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
        self.states[new_index].into_repetition = true;
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

    /// Minimize the push-down automaton.
    ///
    /// Combines states that have the exact same fields. This significantly reduces the size of
    /// larger automaton, but at the const of longer compile time. The algorithm is pretty naive,
    /// just looping through the states repeatedly until it no longer finds states that can be
    /// combined.
    pub(crate) fn minimize(&mut self) {
        loop {
            // Find the set of all distinct and duplicated states. The distinct states will be
            // kept.
            let mut distinct_states = HashMap::new();
            // Note that deleted_states will always be ordered from least to greatest.
            let mut deleted_states = Vec::new();
            for (index, state) in self.states.iter().cloned().enumerate() {
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
