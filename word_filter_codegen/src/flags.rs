use alloc::{format, string::String};
use bitflags::bitflags;

bitflags! {
    /// Bitflags that define attributes on a `State`.
    ///
    /// These flags define specific attributes on a `State`. Multiple flags may be set at the same
    /// time.
    pub(crate) struct Flags: u8 {
        /// The state is matching state, matching a word.
        ///
        /// If this flag is set, a word should be stored within the state as well.
        const WORD = 0b0000_0001;
        /// The state is a matching state, matching an exception.
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
    }
}

impl Flags {
    /// Returns the generated definition of this type.
    pub(crate) fn to_definition(&self) -> String {
        format!("word_filter::pda::Flags::from_bits_truncate({})", self.bits())
    }
}
