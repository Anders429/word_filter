mod node;
mod pointer;

use node::Node;
use pointer::{Pointer, PointerStatus};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    pin::Pin,
};

#[derive(PartialEq)]
pub enum RepeatedCharacterMatchMode {
    AllowRepeatedCharacters,
    DisallowRepeatedCharacters,
}

impl Default for RepeatedCharacterMatchMode {
    fn default() -> Self {
        RepeatedCharacterMatchMode::AllowRepeatedCharacters
    }
}

pub enum CensorMode {
    ReplaceAllWith(char),
}

impl Default for CensorMode {
    fn default() -> Self {
        CensorMode::ReplaceAllWith('*')
    }
}

#[derive(Default)]
pub struct Options {
    pub repeated_character_match_mode: RepeatedCharacterMatchMode,
    pub censor_mode: CensorMode,
}

pub struct WordFilter<'a> {
    root: Node<'a>,
    separator_root: Node<'a>,
    #[allow(dead_code)]
    alias_map: HashMap<String, Pin<Box<Node<'a>>>>,
    options: Options,
}

impl<'a> WordFilter<'a> {
    pub fn new(
        filtered_words: &[&'a str],
        exceptions: &[&'a str],
        separators: &[&str],
        aliases: &[(&'a str, &str)],
        options: Options,
    ) -> Self {
        let mut root = Node::new();

        for word in filtered_words {
            root.add_match(word);
        }

        for word in exceptions {
            root.add_exception(word);
        }

        let mut separator_root = Node::new();
        for word in separators {
            separator_root.add_return(word);
        }

        let mut alias_map = HashMap::new();
        for (value, alias) in aliases {
            alias_map
                .entry(value.to_string())
                .or_insert_with(|| Box::pin(Node::new()))
                .add_return(alias);
        }
        // Find merged aliases.
        let mut queue = VecDeque::new();
        for (value, alias) in aliases {
            for (merge_value, _) in aliases {
                let overlap_value = str_overlap::overlap(alias, merge_value);
                if overlap_value.is_empty() || overlap_value == *merge_value {
                    continue;
                }
                queue.push_back((
                    value.to_string(),
                    merge_value[overlap_value.len()..].to_string(),
                    alias.to_string(),
                ))
            }
        }
        let mut new_aliases = Vec::new();
        while !queue.is_empty() {
            let (value, target_value, alias) = queue.pop_front().unwrap();
            for (new_value, new_alias) in aliases {
                if target_value == *new_alias || new_alias.starts_with(&target_value) {
                    new_aliases
                        .push((value.to_string() + new_value, alias.to_string() + new_alias));
                } else if target_value.starts_with(new_alias) {
                    queue.push_back((
                        value.to_string() + new_value,
                        target_value[new_alias.len()..].to_string(),
                        alias.to_string() + new_alias,
                    ));
                }
            }
        }
        for (value, alias) in new_aliases {
            alias_map
                .entry(value)
                .or_insert_with(|| Box::pin(Node::new()))
                .add_return(&alias);
        }

        // Apply aliases on each other.
        let keys = alias_map.keys().cloned().collect::<Vec<_>>();
        for value in &keys {
            for alias_value in &keys {
                if value == alias_value {
                    continue;
                }
                let alias_node = unsafe {
                    // SAFETY: The obtained reference to a Node is self-referential within the
                    // WordFilter struct. The only reason this conversion from reference to pointer
                    // and back again is necessary is to make the reference lifetime-agnostic to
                    // allow the self-reference. This is safe, because every Node owned in the graph
                    // by the WordFilter is pinned in place in memory, meaning it will only ever
                    // move when the WordFilter is dropped. Therefore, this reference will be valid
                    // for as long as it is used by the WordFilter.
                    (alias_map[alias_value].as_ptr() as *const Node)
                        .as_ref()
                        .unwrap()
                };
                alias_map
                    .get_mut(value)
                    .unwrap()
                    .add_alias(alias_value, alias_node);
            }
        }
        for (value, node) in &alias_map {
            unsafe {
                // SAFETY: The obtained reference to a Node is self-referential within the
                // WordFilter struct. The only reason this conversion from reference to pointer and
                // back again is necessary is to make the reference lifetime-agnostic to allow the
                // self-reference. This is safe, because every Node owned in the graph by the
                // WordFilter is pinned in place in memory, meaning it will only ever move when the
                // WordFilter is dropped. Therefore, this reference will be valid for as long as it
                // is used by the WordFilter.
                root.add_alias(value, (node.as_ptr() as *const Node).as_ref().unwrap());
            }
        }

        Self {
            root,
            separator_root,
            alias_map,
            options,
        }
    }

    fn push_aliases(
        &self,
        pointer: &Pointer<'a>,
        new_pointers: &mut Vec<Pointer<'a>>,
        visited: Vec<&Node>,
    ) {
        for (alias_node, return_node) in &pointer.current_node.aliases {
            if visited.iter().any(|n| std::ptr::eq(*n, *alias_node)) {
                continue;
            }
            let mut return_nodes = pointer.return_nodes.clone();
            return_nodes.push(return_node);
            let alias_pointer = Pointer::new(alias_node, return_nodes, pointer.start, pointer.len);
            let mut new_visited = visited.clone();
            new_visited.push(alias_node);
            self.push_aliases(&alias_pointer, new_pointers, new_visited);
            new_pointers.push(alias_pointer);
        }
    }

    fn find_pointers(&self, input: &str) -> Box<[Pointer]> {
        let mut pointers = vec![Pointer::new(&self.root, Vec::new(), 0, 0)];
        pointers.extend(
            self.root
                .aliases
                .iter()
                .map(|(alias_node, return_node)| Pointer::new(alias_node, vec![return_node], 0, 0)),
        );
        let mut found_matches = Vec::new();
        let mut found_exceptions = Vec::new();
        for (i, c) in input.chars().enumerate() {
            let mut new_pointers = Vec::new();
            for pointer in pointers.iter_mut() {
                let last_pointer = pointer.clone();
                if pointer.step(&c) {
                    new_pointers.push(pointer.clone());

                    if self.options.repeated_character_match_mode
                        == RepeatedCharacterMatchMode::AllowRepeatedCharacters
                    {
                        new_pointers.push(last_pointer);
                    }

                    // Aliases.
                    self.push_aliases(pointer, &mut new_pointers, Vec::new());
                    // Separators.
                    let mut return_nodes = pointer.return_nodes.clone();
                    return_nodes.push(pointer.current_node);
                    new_pointers.push(Pointer::new(
                        &self.separator_root,
                        return_nodes,
                        pointer.start,
                        pointer.len,
                    ));
                } else if let PointerStatus::Match(_) = pointer.status {
                    found_matches.push(pointer.clone());
                } else if let PointerStatus::Exception(_) = pointer.status {
                    found_exceptions.push(pointer.clone());
                }
            }

            // Add root again.
            new_pointers.push(Pointer::new(&self.root, Vec::new(), i + 1, 0));
            new_pointers.extend(self.root.aliases.iter().map(|(alias_node, return_node)| {
                Pointer::new(alias_node, vec![return_node], i + 1, 0)
            }));

            pointers = new_pointers;
        }

        // Evaluate all remaining pointers.
        for pointer in pointers {
            match pointer.status {
                PointerStatus::Match(_) => found_matches.push(pointer.clone()),
                PointerStatus::Exception(_) => found_exceptions.push(pointer.clone()),
                _ => {}
            }
        }

        // TODO: Is there a faster way to do this?
        found_matches
            .iter()
            .filter(|m| {
                let start = m.start;
                let end = start + m.found_len.unwrap();
                !found_exceptions
                    .iter()
                    .any(|e| e.start <= start && e.start + e.found_len.unwrap() >= end)
            })
            .cloned()
            .collect::<Vec<Pointer>>()
            .into_boxed_slice()
    }

    pub fn find(&self, input: &str) -> Box<[&str]> {
        self.find_pointers(input)
            .iter()
            .map(|pointer| {
                if let PointerStatus::Match(s) = pointer.status {
                    s
                } else {
                    ""
                }
            })
            .collect::<HashSet<&str>>()
            .iter()
            .cloned()
            .collect::<Vec<&str>>()
            .into_boxed_slice()
    }

    /// Check whether `input` contains any filtered words.
    ///
    /// Returns `true` if matches are found, and `false` otherwise.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{Options, WordFilter};
    ///
    /// let word_filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());
    ///
    /// assert!(word_filter.check("this string contains foo"));
    /// ```
    pub fn check(&self, input: &str) -> bool {
        !self.find_pointers(input).is_empty()
    }

    /// Censor all filtered words within `input`.
    ///
    /// Returns a newly-allocated `String` with all filtered words censored using the `CensorMode`
    /// strategy, as defined in the `Options` passed to the `WordFilter` at construction.
    ///
    /// Example usage:
    ///
    /// ```
    /// use word_filter::{Options, WordFilter};
    ///
    /// // Note that Options::default() uses CensorMode::ReplaceAllWith('*').
    /// let word_filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());
    ///
    /// assert_eq!(word_filter.censor("this string contains foo"), "this string contains ***");
    /// ```
    pub fn censor(&self, input: &str) -> String {
        let mut output = input.to_string();
        for pointer in self.find_pointers(input).iter() {
            let mut new_output = String::with_capacity(output.len());
            let start = pointer.start;
            let end = start + pointer.found_len.unwrap();
            for (i, c) in output.chars().enumerate() {
                if i < start || i > end {
                    new_output.push(c);
                } else {
                    match self.options.censor_mode {
                        CensorMode::ReplaceAllWith(c) => new_output.push(c),
                    }
                }
            }
            output = new_output;
        }
        output
    }
}

#[cfg(test)]
mod tests {
    use crate::{CensorMode, Options, RepeatedCharacterMatchMode, WordFilter};

    #[test]
    fn find() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn check() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());

        assert!(filter.check("foo"));
    }

    #[test]
    fn censor() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[], Options::default());

        assert_eq!(filter.censor("foo"), "***");
    }

    #[test]
    fn exceptions() {
        let filter = WordFilter::new(
            &["foo"],
            &["afoo", "foob", "cfood"],
            &[],
            &[],
            Options::default(),
        );

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("afoo"), Vec::new().into_boxed_slice());
        assert_eq!(filter.find("foob"), Vec::new().into_boxed_slice());
        assert_eq!(filter.find("cfood"), Vec::new().into_boxed_slice());
    }

    #[test]
    fn exceptions_and_matches() {
        let filter = WordFilter::new(&["foo"], &["foobar"], &[], &[], Options::default());

        assert_eq!(filter.find("foobarfoo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn separators() {
        let filter = WordFilter::new(&["foo"], &[], &[" "], &[], Options::default());

        assert_eq!(filter.find("f oo"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn aliases() {
        let filter = WordFilter::new(&["foo"], &[], &[], &[("o", "a")], Options::default());

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fao"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("foa"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("faa"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn aliases_on_aliases() {
        let filter = WordFilter::new(
            &["foo"],
            &[],
            &[],
            &[("o", "a"), ("a", "b")],
            Options::default(),
        );

        assert_eq!(filter.find("foo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fbo"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fob"), vec!["foo"].into_boxed_slice());
        assert_eq!(filter.find("fbb"), vec!["foo"].into_boxed_slice());
    }

    #[test]
    fn merged_aliases() {
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[("b", "cd"), ("a", "ef"), ("de", "g")],
            Options::default(),
        );

        assert_eq!(filter.find("cgfr"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn recursive_alias_no_overflow() {
        // Make sure recursive aliases don't cause a stack overflow.
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[("a", "b"), ("b", "a")],
            Options {
                repeated_character_match_mode:
                    RepeatedCharacterMatchMode::DisallowRepeatedCharacters,
                censor_mode: CensorMode::ReplaceAllWith('*'),
            },
        );

        assert_eq!(filter.find("abr"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn options_repeated_characters_allowed() {
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[],
            Options {
                repeated_character_match_mode: RepeatedCharacterMatchMode::AllowRepeatedCharacters,
                censor_mode: CensorMode::ReplaceAllWith('*'),
            },
        );

        assert_eq!(filter.find("bbbaaaarrrr"), vec!["bar"].into_boxed_slice());
    }

    #[test]
    fn options_repeated_characters_disallowed() {
        let filter = WordFilter::new(
            &["bar"],
            &[],
            &[],
            &[],
            Options {
                repeated_character_match_mode:
                    RepeatedCharacterMatchMode::DisallowRepeatedCharacters,
                censor_mode: CensorMode::ReplaceAllWith('*'),
            },
        );

        assert_eq!(filter.find("bbbaaaarrrr"), vec![].into_boxed_slice());
    }

    #[test]
    fn options_censor_mode() {
        let filter = WordFilter::new(
            &["foo"],
            &[],
            &[],
            &[],
            Options {
                repeated_character_match_mode: RepeatedCharacterMatchMode::AllowRepeatedCharacters,
                censor_mode: CensorMode::ReplaceAllWith('#'),
            },
        );

        assert_eq!(filter.censor("foo"), "###");
    }
}
