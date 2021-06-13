//! Internal structs for the push-down automaton system.
//!
//! The [`WordFilter`] is internally a nondeterministic push-down automaton. The structs here
//! define the various parts of the system, including states, state types, transitions between
//! states, and stack manipulations. Additionally, instantaneous descriptions are defined to be
//! used during computation.
//!
//! Some of the structs here are made publicly visible to allow for access by code generation.
//! However, none of the structs here should be relied upon. They are not guaranteed by semver and
//! may change at any time.

#![doc(hidden)]

use alloc::{vec, vec::Vec};
use by_address::ByAddress;
use core::ops::{Bound, RangeBounds};
use debug_unreachable::debug_unreachable;
use hashbrown::HashSet;

/// The different types of states.
///
/// Note that Word and Exception states are considered accepting states.
#[derive(Debug)]
pub enum Type<'a> {
    /// A standard state.
    None,
    /// Indicates a matching state, matching the stored word.
    Word(&'a str),
    /// Indicates a matching state that is an exception.
    Exception,
    /// A return state.
    ///
    /// Traversal from this state will pop the top-most state on the stack and traverse to it.
    Return,
    /// A separator return state.
    ///
    /// This is nearly the same as a Return state, but it also pushes an AppendedSeparator onto the
    /// stack. This indicates that the traversal came from a separator.
    SeparatorReturn,
}

/// Stack-related enums.
mod stack {
    use super::State;

    /// A value on the stack.
    #[derive(Clone, Debug)]
    pub(super) enum Value<'a> {
        /// Indicates the absence of a value.
        ///
        /// This is used when the stack is empty.
        None,
        /// A return state.
        ///
        /// States stored here are returned to at `Return` or `SeparatorReturn` nodes.
        Return(&'a State<'a>),
        /// An appended separator marker.
        ///
        /// This indicates that the previously-matched characters were matched in a separator, and
        /// therefore should not be included if the current state is a Word or Exception.
        AppendedSeparator,
    }

    /// Defines a manipulation of the stack.
    #[derive(Debug)]
    pub(super) enum Manipulation<'a> {
        /// Pushes a value to the stack.
        Push(Value<'a>),
        /// Pops the top value of the stack.
        Pop,
    }
}

/// A transition between states.
#[derive(Debug)]
struct Transition<'a> {
    /// The state being transitioned to.
    state: &'a State<'a>,
    /// Manipulations to the stack that should occur if this transition is taken.
    stack_manipulations: Vec<stack::Manipulation<'a>>,
}

/// A valid state within the push-down automaton.
///
/// This struct contains information about the state and the transitions that can be made from it.
///
/// `c_transitions` and `repetition` define character transitions, while `separator`, `aliases`,
/// and `graphemes` define ε-transitions.
#[derive(Debug)]
pub struct State<'a> {
    /// The state's type.
    pub r#type: Type<'a>,
    /// Direct character transitions.
    ///
    /// Each character can only transition to one other state directly.
    pub c_transitions: fn(char) -> Option<&'a State<'a>>,
    /// A possible repetition transition.
    ///
    /// When transitioning along this character, computation can return back to the previous state
    /// that is stored here.
    pub repetition: Option<(char, &'a State<'a>)>,
    /// The separator state that may be entered from this state.
    ///
    /// The absence of a separator state indicates that this state cannot enter into a separator.
    /// This is possible in, for example, graphemes or other separators.
    pub separator: Option<&'a State<'a>>,
    /// Alias states and their accompanying return states.
    ///
    /// These are pairs of the form (alias_state, return_state). When computation traversed to
    /// `alias_state`, `return_state` should be pushed to the stack.
    pub aliases: &'a [(&'a State<'a>, &'a State<'a>)],
    /// Grapheme states.
    ///
    /// These are states that are traversed to from this state via ε-transitions. They are still
    /// direct paths from this state, but traverse down grapheme paths which must be handled
    /// different from c_transitions.
    pub graphemes: &'a [&'a State<'a>],
}

impl<'a> State<'a> {
    /// Transition using the given input character `c` with the top-of-stack value `s`.
    ///
    /// To perform an ε-transition, a `None` value should be provided for the parameter `c`.
    #[inline]
    fn transitions(&'a self, c: Option<char>, s: stack::Value<'a>) -> Vec<Transition<'a>> {
        let mut result = Vec::new();

        match c {
            Some(c) => {
                if let Some(state) = (self.c_transitions)(c) {
                    result.push(Transition {
                        state,
                        stack_manipulations: vec![],
                    })
                }
                if let Some(repetition) = self.repetition {
                    if repetition.0 == c {
                        result.push(Transition {
                            state: repetition.1,
                            stack_manipulations: vec![],
                        })
                    }
                }
            }
            None => {
                if let Some(state) = self.separator {
                    result.push(Transition {
                        state,
                        stack_manipulations: vec![stack::Manipulation::Push(stack::Value::Return(
                            self,
                        ))],
                    });
                }
                for alias in self.aliases {
                    result.push(Transition {
                        state: alias.0,
                        stack_manipulations: vec![stack::Manipulation::Push(stack::Value::Return(
                            alias.1,
                        ))],
                    });
                }
                for grapheme in self.graphemes {
                    result.push(Transition {
                        state: grapheme,
                        stack_manipulations: vec![],
                    })
                }

                match self.r#type {
                    Type::Return => match s {
                        stack::Value::Return(state) => {
                            result.push(Transition {
                                state,
                                stack_manipulations: vec![stack::Manipulation::Pop],
                            });
                        }
                        _ => {}
                    },
                    Type::SeparatorReturn => match s {
                        stack::Value::Return(state) => {
                            result.push(Transition {
                                state,
                                stack_manipulations: vec![
                                    stack::Manipulation::Pop,
                                    stack::Manipulation::Push(stack::Value::AppendedSeparator),
                                ],
                            });
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
        }

        match s {
            stack::Value::AppendedSeparator => {
                for transition in result.iter_mut() {
                    transition
                        .stack_manipulations
                        .insert(0, stack::Manipulation::Pop);
                }
            }
            _ => {}
        }

        result
    }
}

/// An instantaneous description (ID) of a specific instant in computation.
///
/// An instantaneous description stored the current state, the current stack, and the range of
/// characters which have been traversed.
///
/// During computation, multiple IDs will exist at the same time, representing the different paths
/// that are being traversed simultaneously due to the nondeterministic nature of the push-down
/// automaton.
#[derive(Clone, Debug)]
pub(crate) struct InstantaneousDescription<'a> {
    /// The current state.
    state: &'a State<'a>,
    /// The current stack.
    stack: Vec<stack::Value<'a>>,
    /// The index within the input where this computation started.
    start: usize,
    /// The current end index, marking the range of input that has been computed.
    end: usize,
}

impl<'a> InstantaneousDescription<'a> {
    /// Creates a new Instantaneous Description, starting from `state` with computation beginning
    /// at index `start` in the input.
    pub(crate) fn new(state: &'a State<'a>, start: usize) -> Self {
        Self {
            state,
            stack: Vec::new(),
            start,
            end: start,
        }
    }

    /// Return whether the current state is an accepting state.
    ///
    /// Whether the state is accepting is actually dependent on both the state's type and the top
    /// of the stack. If the top of the stack is AppendedSeparator, then the state cannot be
    /// accepting. Otherwise, the state is accepting is the type is Word or Exception.
    #[inline]
    pub(crate) fn is_accepting(&self) -> bool {
        matches!(self.state.r#type, Type::Word(_) | Type::Exception)
            && !matches!(
                self.stack.last().unwrap_or(&stack::Value::None),
                stack::Value::AppendedSeparator
            )
    }

    /// Return whether the state is a word.
    #[inline]
    pub(crate) fn is_word(&self) -> bool {
        matches!(self.state.r#type, Type::Word(_))
    }

    /// Unwrap the word that is contained in the state's type.
    ///
    /// This is undefined behavior if the state's type is not Word. This must be checked prior to
    /// calling.
    #[inline]
    pub(crate) unsafe fn unwrap_word_unchecked(self) -> &'a str {
        match self.state.r#type {
            Type::Word(s) => s,
            _ => debug_unreachable!(),
        }
    }

    /// Return the start index.
    #[inline]
    pub(crate) fn start(&self) -> usize {
        self.start
    }

    /// Return the end index.
    #[inline]
    pub(crate) fn end(&self) -> usize {
        self.end
    }

    /// Transition using the input character `c`.
    ///
    /// If an ε-transition is desired, `None` should be provided for `c`.
    pub(crate) fn transition(
        &self,
        c: Option<char>,
        visited: &mut HashSet<ByAddress<&State<'a>>>,
    ) -> impl Iterator<Item = InstantaneousDescription<'a>> {
        let mut new_ids = Vec::new();
        for transition in self
            .state
            .transitions(c, self.stack.last().unwrap_or(&stack::Value::None).clone())
            .iter()
        {
            if !visited.contains(&ByAddress(transition.state)) {
                let mut new_id = self.clone();
                new_id.state = transition.state;
                for manipulation in &transition.stack_manipulations {
                    match manipulation {
                        stack::Manipulation::Push(value) => new_id.stack.push(value.clone()),
                        stack::Manipulation::Pop => {
                            new_id.stack.pop();
                        }
                    }
                }
                // ε-transitions.
                visited.insert(ByAddress(transition.state));
                new_ids.extend(new_id.transition(None, visited));
                visited.remove(&ByAddress(transition.state));

                new_ids.push(new_id);
            }
        }
        new_ids.into_iter()
    }

    /// Step along the input `c`.
    pub(crate) fn step(mut self, c: char) -> impl Iterator<Item = InstantaneousDescription<'a>> {
        self.end += 1;
        self.transition(Some(c), &mut HashSet::new())
    }
}

/// Define RangeBounds for an Instantaneous Description.
///
/// This defines the range of input that was consumed by the ID. This is useful for nesting the IDs
/// using a nested containment list, which requires that RangeBounds are defined.
impl RangeBounds<usize> for InstantaneousDescription<'_> {
    /// The start bound, which is always inclusive.
    #[inline]
    fn start_bound(&self) -> Bound<&usize> {
        Bound::Included(&self.start)
    }

    /// The end bound. This is always exclusive, except when the state's type is Exception, in
    /// which case it is inclusive. This is to ensure that Exceptions take precedence over Words.
    #[inline]
    fn end_bound(&self) -> Bound<&usize> {
        match self.state.r#type {
            Type::Exception => Bound::Included(&self.end),
            _ => Bound::Excluded(&self.end),
        }
    }
}
