#![no_std]

extern crate alloc;

mod node;

use alloc::{
    borrow::ToOwned,
    collections::VecDeque,
    format,
    string::{String, ToString},
    vec::Vec,
};
use hashbrown::HashMap;
use node::NodeGenerator;
use str_overlap::Overlap;

#[derive(Debug)]
pub enum Visibility {
    Private,
    Pub,
    PubCrate,
    PubIn(String),
}

impl Default for Visibility {
    fn default() -> Self {
        Self::Private
    }
}

impl ToString for Visibility {
    fn to_string(&self) -> String {
        match self {
            Visibility::Private => String::new(),
            Visibility::Pub => "pub".to_owned(),
            Visibility::PubCrate => "pub(crate)".to_owned(),
            Visibility::PubIn(path) => format!("pub(in {})", path),
        }
    }
}

fn generate_nodes(nodes: &Vec<NodeGenerator>, identifier: &str) -> String {
    let mut result = "[".to_owned();

    result.push_str(&nodes.into_iter().map(|node| node.generate(identifier)).collect::<Vec<_>>().join(",\n    "));

    result.push_str("]");

    result
}

#[derive(Debug, Default)]
pub struct WordFilterGenerator {
    words: Vec<String>,
    exceptions: Vec<String>,
    separators: Vec<String>,
    aliases: Vec<(String, String)>,
    visibility: Visibility,
}

impl WordFilterGenerator {
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn word<S>(&mut self, word: &S) -> &mut Self
    where
        S: ToString + ?Sized,
    {
        self.words.push(word.to_string());
        self
    }

    #[inline]
    pub fn words<I, S>(&mut self, words: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: ToString,
    {
        self.words.extend(words.into_iter().map(|s| s.to_string()));
        self
    }

    #[inline]
    pub fn exception<S>(&mut self, exception: &S) -> &mut Self
    where
        S: ToString + ?Sized,
    {
        self.exceptions.push(exception.to_string());
        self
    }

    #[inline]
    pub fn exceptions<I, S>(&mut self, exceptions: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: ToString,
    {
        self.exceptions
            .extend(exceptions.into_iter().map(|s| s.to_string()));
        self
    }

    #[inline]
    pub fn separator<S>(&mut self, separator: &S) -> &mut Self
    where
        S: ToString + ?Sized,
    {
        self.separators.push(separator.to_string());
        self
    }

    #[inline]
    pub fn separators<I, S>(&mut self, separators: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: ToString,
    {
        self.separators
            .extend(separators.into_iter().map(|s| s.to_string()));
        self
    }

    #[inline]
    pub fn alias<S, T>(&mut self, source: &S, alias: &T) -> &mut Self
    where
        S: ToString + ?Sized,
        T: ToString + ?Sized,
    {
        self.aliases.push((source.to_string(), alias.to_string()));
        self
    }

    #[inline]
    pub fn aliases<'b, I, S, T>(&mut self, aliases: I) -> &mut Self
    where
        I: IntoIterator<Item = &'b (S, T)>,
        S: ToString + 'b,
        T: ToString + 'b,
    {
        self.aliases.extend(
            aliases
                .into_iter()
                .map(|(s, t)| (s.to_string(), t.to_string())),
        );
        self
    }

    #[inline]
    pub fn visibility(&mut self, visibility: Visibility) -> &mut Self {
        self.visibility = visibility;
        self
    }

    pub fn generate(&self, identifier: &str) -> String {
        let mut root = NodeGenerator::default();
        let mut separator_root = NodeGenerator::default();
        // TODO: Either find a way to approximate capacity or remove the issue of reallocation
        // after mutation in `add_path()`.
        let mut nodes = Vec::with_capacity(2048);

        for word in &self.words {
            root.add_match(word, &mut nodes);
        }

        for exception in &self.exceptions {
            root.add_exception(exception, &mut nodes);
        }

        extern crate std;
        std::dbg!(&nodes);

        for separator in &self.separators {
            separator_root.add_return(separator, &mut nodes);
        }

        let mut alias_map = HashMap::new();
        for (value, alias) in &self.aliases {
            alias_map
                .entry(value.clone())
                .or_insert_with(|| NodeGenerator::default())
                .add_return(alias, &mut nodes);
        }
        // Find merged aliases.
        // First, find all aliases that can possibly be combined by a value.
        let mut queue = VecDeque::new();
        for (value, alias) in &self.aliases {
            for (merge_value, _) in &self.aliases {
                let overlap_value = alias.overlap_end(merge_value);
                if overlap_value.is_empty() || overlap_value == *merge_value {
                    continue;
                }
                queue.push_back((
                    value.clone(),
                    unsafe {
                        // SAFETY: `overlap_value` will always be the prefix of `merge_value`.
                        // Therefore, this will never be out of bounds and it will always uphold
                        // `str` invariants.
                        merge_value.get_unchecked(overlap_value.len()..).to_owned()
                    },
                    alias.clone(),
                ));
            }
        }
        // Now, find aliases that complete the combination.
        let mut new_aliases = Vec::new();
        while let Some((value, target_value, alias)) = queue.pop_front() {
            for (new_value, new_alias) in &self.aliases {
                if target_value == *new_alias || new_alias.starts_with(&target_value) {
                    new_aliases.push((value.clone() + new_value, alias.clone() + new_alias));
                } else if target_value.starts_with(new_alias) {
                    // If the combination isn't complete, push it to the queue and try again.
                    queue.push_back((
                        value.clone() + new_value,
                        unsafe {
                            // SAFETY: Since `new_alias` is the prefix of `target_value`, this will
                            // never be out of bounds and will always uphold `str` invariants.
                            target_value.get_unchecked(new_alias.len()..).to_owned()
                        },
                        alias.clone() + new_alias,
                    ));
                }
            }
        }
        for (value, alias) in new_aliases {
            alias_map
                .entry(value)
                .or_insert_with(|| NodeGenerator::default())
                .add_return(&alias, &mut nodes);
        }

        // Add aliases to nodes list.
        let mut indexed_aliases = Vec::new();
        for (value, alias) in alias_map {
            indexed_aliases.push((value, nodes.len()));
            nodes.push(alias);
        }

        // Apply aliases on each other.
        for (value, index) in indexed_aliases.iter().cloned() {
            for (alias_value, alias_index) in &indexed_aliases {
                if value == *alias_value {
                    continue;
                }
                unsafe {(&mut nodes[index] as *mut NodeGenerator).as_mut()}.unwrap().add_alias(alias_value, &mut nodes, *alias_index);
            }
        }

        // Apply aliases on root.
        for (value, index) in indexed_aliases {
            root.add_alias(&value, &mut nodes, index);
        }

        format!(
            "{} static {}: ::word_filter::WordFilter<{}> = ::word_filter::WordFilter {{
    root: {},
    separator_root: {},
    nodes: {},
}};",
            self.visibility.to_string(),
            identifier,
            nodes.len(),
            root.generate(identifier),
            separator_root.generate(identifier),
            generate_nodes(&nodes, identifier),
        )
    }
}


