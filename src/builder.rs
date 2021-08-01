use alloc::{string::String, vec::Vec};
use bitflags::bitflags;

bitflags! {
    pub struct SeparatorFlags: u8 {
        /// Allow separators when matching words.
        const BETWEEN_WORDS = 0x0000_0001;
        /// Allow separators when matching exceptions.
        const BETWEEN_EXCEPTIONS = 0x0000_0010;
    }
}

pub struct WordFilterBuilder {
    words: Vec<String>,
    exceptions: Vec<String>,
    separators: Vec<String>,
    aliases: Vec<(String, String)>,
    separator_flags: SeparatorFlags,
}

impl WordFilterBuilder {
    pub const fn new() -> Self {
        Self {
            words: Vec::new(),
            exceptions: Vec::new(),
            separators: Vec::new(),
            aliases: Vec::new(),
            separator_flags: SeparatorFlags::all(), 
        }
    }
}
