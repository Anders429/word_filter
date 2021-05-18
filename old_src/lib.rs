#[no_std]

extern crate alloc;

pub mod censor;
pub mod node;

use core::fmt;
use node::Node;

#[derive(Clone, Copy, Debug)]
pub enum RepeatedCharacterMatchMode {
    AllowRepeatedCharacters,
    DisallowRepeatedCharacters,
}

pub struct WordFilter<'a, const N: usize> {
    pub root: Node<'a>,
    pub separator_root: Node<'a>,
    pub nodes: [Node<'a>; N],
    pub repeated_character_match_mode: RepeatedCharacterMatchMode,
    pub censor: fn(&str) -> String,
}

impl<const N: usize> fmt::Debug for WordFilter<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WordFilter")
            .field("root", &self.root)
            .field("separator_root", &self.separator_root)
            .field("nodes", &self.nodes)
            .field(
                "repeated_character_match_mode",
                &self.repeated_character_match_mode,
            )
            .field("censor", &(self.censor as usize as *const ()))
            .finish()
    }
}
