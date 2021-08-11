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
use bitflags::bitflags;
use by_address::ByAddress;
use const_fn_assert::{cfn_assert, cfn_assert_eq};
use core::{
    ops::{Bound, RangeBounds},
    ptr,
};
use debug_unreachable::debug_unreachable;
use hashbrown::HashSet;

bitflags! {
    /// Bitflags that define attributes on a [`State`].
    ///
    /// These flags define boolean attributes on a `State`. Multiple flags may be set at the same
    /// time.
    pub struct Flags: u8 {
        /// The state is a matching state, matching a word.
        ///
        /// If this flag is set, a word should be stored within the state as well.
        ///
        /// This flag cannot be set if `EXCEPTION` is set.
        const WORD = 0b0000_0001;
        /// The state is a matching state, matching an exception.
        ///
        /// This flag cannot be set if `WORD` is set.
        const EXCEPTION = 0b0000_0010;
        /// This is a separator state, existing within a separator subroutine.
        const SEPARATOR = 0b0000_0100;
        /// [`InstantaneousDescription`]s can return from this state.
        const RETURN = 0b0000_1000;
        /// This state can be repeated to.
        const INTO_REPETITION = 0b0001_0000;
        /// This state can process a repetition on the stack.
        const TAKE_REPETITION = 0b0010_0000;
        /// This state can enter a separator subroutine.
        const INTO_SEPARATOR = 0b0100_0000;

        /// This state is an accepting state.
        ///
        /// This is the same as saying the state is a matching state. A state should not be set
        /// with these flags, as it would set both the `WORD` and `EXCEPTION` bits, which is not
        /// valid for constructing a state.
        const ACCEPTING = Flags::WORD.bits() | Flags::EXCEPTION.bits();
        /// All flags defining a state type.
        const STATE_TYPES = Self::WORD.bits() | Self::EXCEPTION.bits() | Self::SEPARATOR.bits() | Self::RETURN.bits();
    }
}

/// Attributes of a [`State`].
///
/// Contains binary flags and an optional string containing the `State`'s matched word.
///
/// Having these attributes stored together ensures that invariants can be upheld on the flags and
/// the associated word. The `WORD` flag will invariantly be set when the `word` field is not
/// `None`, and the `WORD` and `EXCEPTION` flags will never be set at the same time.
#[derive(Debug)]
pub struct Attributes<'a> {
    /// Flags defining binary attributes.
    flags: Flags,
    /// A possible associated word with the state.
    ///
    /// This will be provided if and only if the `WORD` flag is present in `flags`.
    word: Option<&'a str>,
}

impl<'a> Attributes<'a> {
    /// Create a new `Attributes` struct containing the given `flags` and `word`.
    ///
    /// This associated function checks that the following invariants are upheld:
    /// - If the `WORD` flag is set, then `word` must not be `None`.
    /// - The `WORD` and `EXCEPTION` flags cannot both be set.
    ///
    /// If a strange error is encountered within this method, it is likely one of these invariants
    /// is not upheld. The strangeness of the error is consequential of the difficulty is asserting
    /// values at compile-time.
    pub const fn new(flags: Flags, word: Option<&'a str>) -> Self {
        // If this errors with some weird error, it means that the invariant between the WORD flag
        // and the `word` attribute is not upheld.
        cfn_assert_eq!(flags.contains(Flags::WORD), word.is_some());

        // Same as above, but with regards to only one accepting flag.
        cfn_assert!(!flags.contains(Flags::ACCEPTING));

        Self { flags, word }
    }

    /// Returns whether the `WORD` flag is set.
    #[inline]
    fn word(&self) -> bool {
        self.flags.contains(Flags::WORD)
    }

    /// Returns whether the `EXCEPTION` flag is set.
    #[inline]
    fn exception(&self) -> bool {
        self.flags.contains(Flags::EXCEPTION)
    }

    /// Returns whether the `SEPARATOR` flag is set.
    #[inline]
    fn separator(&self) -> bool {
        self.flags.contains(Flags::SEPARATOR)
    }

    /// Returns whether the `RETURN` flag is set.
    #[inline]
    fn r#return(&self) -> bool {
        self.flags.contains(Flags::RETURN)
    }

    /// Returns whether the `INTO_REPETITION` flag is set.
    #[inline]
    fn into_repetition(&self) -> bool {
        self.flags.contains(Flags::INTO_REPETITION)
    }

    /// Returns whether the `TAKE_REPETITION` flag is set.
    #[inline]
    fn take_repetition(&self) -> bool {
        self.flags.contains(Flags::TAKE_REPETITION)
    }

    /// Returns whether the `INTO_SEPARATOR` flag is set.
    #[inline]
    fn into_separator(&self) -> bool {
        self.flags.contains(Flags::INTO_SEPARATOR)
    }

    /// Returns whether one of the `WORD` or `EXCEPTION` flags are set.
    #[inline]
    fn accepting(&self) -> bool {
        self.flags.intersects(Flags::ACCEPTING)
    }
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
        /// A target state.
        ///
        /// States stored here must be hit before they are popped. These are pushed in repetition
        /// handling to ensure the same path is repeated.
        Target(&'a State<'a>),
        Repetition(&'a State<'a>),
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
    /// The state's associated attributes.
    pub attributes: Attributes<'a>,
    /// Direct character transitions.
    ///
    /// Each character can only transition to one other state directly.
    pub c_transitions: fn(char) -> Option<&'a State<'a>>,
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
    /// Returns whether the state can be repeated to.
    #[inline]
    fn into_repetition(&self) -> bool {
        self.attributes.into_repetition()
    }

    /// Returns whether the state can process a repetition on the stack.
    #[inline]
    fn take_repetition(&self) -> bool {
        self.attributes.take_repetition()
    }

    /// Returns whether the state can enter a separator.
    #[inline]
    fn into_separator(&self) -> bool {
        self.attributes.into_separator()
    }

    /// Transition using the given input character `c` with the top-of-stack value `s`.
    ///
    /// To perform an ε-transition, a `None` value should be provided for the parameter `c`.
    #[inline]
    fn transitions(
        &'a self,
        c: Option<char>,
        s: stack::Value<'a>,
        separator: &'a State<'a>,
    ) -> Vec<Transition<'a>> {
        let mut result = Vec::new();

        match s {
            stack::Value::Repetition(repetition_state) => {
                match c {
                    Some(c) => {
                        if !self.take_repetition() {
                            if let Some(state) = (self.c_transitions)(c) {
                                result.push(Transition {
                                    state,
                                    stack_manipulations: vec![],
                                });
                                if self.into_repetition() {
                                    result.push(Transition {
                                        state,
                                        stack_manipulations: vec![stack::Manipulation::Push(
                                            stack::Value::Repetition(self),
                                        )],
                                    });
                                }
                            }
                        }
                    }
                    None => {
                        if self.into_separator() {
                            result.push(Transition {
                                state: separator,
                                stack_manipulations: vec![stack::Manipulation::Push(
                                    stack::Value::Return(self),
                                )],
                            });
                        }
                        if self.take_repetition() {
                            // Take the repetition.
                            result.push(Transition {
                                state: repetition_state,
                                stack_manipulations: vec![
                                    stack::Manipulation::Pop,
                                    stack::Manipulation::Push(stack::Value::Target(self)),
                                ],
                            })
                        } else {
                            for alias in self.aliases {
                                result.push(Transition {
                                    state: alias.0,
                                    stack_manipulations: vec![stack::Manipulation::Push(
                                        stack::Value::Return(alias.1),
                                    )],
                                });
                                if self.into_repetition() {
                                    result.push(Transition {
                                        state: alias.0,
                                        stack_manipulations: vec![
                                            stack::Manipulation::Push(stack::Value::Repetition(
                                                self,
                                            )),
                                            stack::Manipulation::Push(stack::Value::Return(
                                                alias.1,
                                            )),
                                        ],
                                    })
                                }
                            }
                            for grapheme in self.graphemes {
                                result.push(Transition {
                                    state: grapheme,
                                    stack_manipulations: vec![],
                                });
                            }
                        }
                    }
                }
            }
            stack::Value::Target(target_state) => match c {
                Some(c) => {
                    if let Some(state) = (self.c_transitions)(c) {
                        if state.take_repetition() {
                            if ptr::eq(state, target_state) {
                                result.push(Transition {
                                    state,
                                    stack_manipulations: vec![stack::Manipulation::Pop],
                                });
                                if self.into_repetition() {
                                    result.push(Transition {
                                        state,
                                        stack_manipulations: vec![
                                            stack::Manipulation::Pop,
                                            stack::Manipulation::Push(stack::Value::Repetition(
                                                self,
                                            )),
                                        ],
                                    });
                                }
                            }
                        } else {
                            result.push(Transition {
                                state,
                                stack_manipulations: vec![],
                            });
                            if self.into_repetition() {
                                result.push(Transition {
                                    state,
                                    stack_manipulations: vec![stack::Manipulation::Push(
                                        stack::Value::Repetition(self),
                                    )],
                                });
                            }
                        }
                    }
                }
                None => {
                    for alias in self.aliases {
                        if ptr::eq(alias.1, target_state) {
                            result.push(Transition {
                                state: alias.0,
                                stack_manipulations: vec![
                                    stack::Manipulation::Pop,
                                    stack::Manipulation::Push(stack::Value::Return(alias.1)),
                                ],
                            });
                            if self.into_repetition() {
                                result.push(Transition {
                                    state: alias.0,
                                    stack_manipulations: vec![
                                        stack::Manipulation::Pop,
                                        stack::Manipulation::Push(stack::Value::Repetition(self)),
                                        stack::Manipulation::Push(stack::Value::Return(alias.1)),
                                    ],
                                });
                            }
                        }
                    }
                }
            },
            _ => match c {
                Some(c) => {
                    if let Some(state) = (self.c_transitions)(c) {
                        result.push(Transition {
                            state,
                            stack_manipulations: vec![],
                        });
                        if self.into_repetition() {
                            result.push(Transition {
                                state,
                                stack_manipulations: vec![stack::Manipulation::Push(
                                    stack::Value::Repetition(self),
                                )],
                            });
                        }
                    }
                }
                None => {
                    if self.into_separator() {
                        result.push(Transition {
                            state: separator,
                            stack_manipulations: vec![stack::Manipulation::Push(
                                stack::Value::Return(self),
                            )],
                        });
                    }
                    for alias in self.aliases {
                        result.push(Transition {
                            state: alias.0,
                            stack_manipulations: vec![stack::Manipulation::Push(
                                stack::Value::Return(alias.1),
                            )],
                        });
                        if self.into_repetition() {
                            result.push(Transition {
                                state: alias.0,
                                stack_manipulations: vec![
                                    stack::Manipulation::Push(stack::Value::Repetition(self)),
                                    stack::Manipulation::Push(stack::Value::Return(alias.1)),
                                ],
                            });
                        }
                    }
                    for grapheme in self.graphemes {
                        result.push(Transition {
                            state: grapheme,
                            stack_manipulations: vec![],
                        });
                    }

                    if self.attributes.r#return() {
                        if let stack::Value::Return(state) = s {
                            result.push(Transition {
                                state,
                                stack_manipulations: vec![stack::Manipulation::Pop],
                            });
                        }
                    }
                }
            },
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
    pub state: &'a State<'a>,
    /// The current stack.
    stack: Vec<stack::Value<'a>>,
    /// The index within the input where this computation started.
    start: usize,
    /// The current end index, marking the range of input that has been computed.
    end: usize,
    /// Whether the computation is within a separator grapheme.
    ///
    /// A separator grapheme is defined as a grapheme that starts on a Separator or SeparatorReturn
    /// state.
    separator_grapheme: bool,
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
            separator_grapheme: false,
        }
    }

    /// Return whether the instantaneous description is an accepting state.
    ///
    /// An Instantaneous Description is accepting if it has an accepting state (Word or Exception),
    /// if the stack is empty, and if the computation is not currently within a separator grapheme.
    #[inline]
    pub(crate) fn is_accepting(&self) -> bool {
        self.state.attributes.accepting() && self.stack.is_empty() && !self.separator_grapheme
    }

    /// Return whether the state is a word.
    #[inline]
    pub(crate) fn is_word(&self) -> bool {
        self.state.attributes.word()
    }

    /// Unwrap the word that is contained in the state's type.
    ///
    /// This is undefined behavior if the state's type is not Word. This must be checked prior to
    /// calling.
    #[inline]
    pub(crate) unsafe fn unwrap_word_unchecked(self) -> &'a str {
        match self.state.attributes.word {
            Some(word) => word,
            None => debug_unreachable!(),
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

    /// Internal transition method, with visited context.
    ///
    /// This allows transitions to keep track of which states have already been visited to prevent
    /// getting stuck in infinite loops.
    fn transition_with_visited(
        &self,
        c: Option<char>,
        separator: &'a State<'a>,
        visited: &mut HashSet<ByAddress<&State<'a>>>,
    ) -> impl Iterator<Item = InstantaneousDescription<'a>> {
        let mut new_ids = Vec::new();
        for transition in self
            .state
            .transitions(
                c,
                self.stack.last().unwrap_or(&stack::Value::None).clone(),
                separator,
            )
            .iter()
        {
            if !visited.contains(&ByAddress(transition.state))
                || transition.state.attributes.r#return()
            {
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
                new_ids.extend(new_id.transition_with_visited(None, separator, visited));
                visited.remove(&ByAddress(transition.state));

                new_ids.push(new_id);
            }
        }
        new_ids.into_iter()
    }

    /// Transition using the input character `c`.
    ///
    /// If an ε-transition is desired, `None` should be provided for `c`.
    #[inline]
    pub(crate) fn transition(
        &self,
        c: Option<char>,
        separator: &'a State<'a>,
    ) -> impl Iterator<Item = InstantaneousDescription<'a>> {
        self.transition_with_visited(c, separator, &mut HashSet::new())
    }

    /// Step along the input `c`.
    pub(crate) fn step(
        mut self,
        c: char,
        separator: &'a State<'a>,
        new_grapheme: bool,
    ) -> impl Iterator<Item = InstantaneousDescription<'a>> {
        self.end += c.len_utf8();
        if new_grapheme {
            self.separator_grapheme = self.state.attributes.separator();
        }
        self.transition(Some(c), separator)
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
        if self.state.attributes.exception() {
            Bound::Included(&self.end)
        } else {
            Bound::Excluded(&self.end)
        }
    }
}
