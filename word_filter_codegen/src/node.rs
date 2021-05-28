use alloc::{borrow::ToOwned, format, string::String, vec, vec::Vec};
use debug_unreachable::debug_unreachable;
use hashbrown::HashMap;
use unicode_segmentation::UnicodeSegmentation;

#[derive(Debug)]
struct Reference(usize);

impl Reference {
    pub(crate) fn generate(&self, identifier: &str) -> String {
        format!("&{}.nodes[{}]", identifier, self.0)
    }
}

#[derive(Debug)]
enum Type<'a> {
    Standard,
    Match(&'a str),
    Exception(&'a str),
    Return,
}

impl Type<'_> {
    fn generate(&self) -> String {
        match self {
            Type::Standard => "Type::Standard".to_owned(),
            Type::Match(word) => format!("Type::Match(\"{}\")", word),
            Type::Exception(exception) => format!("Type::Exception(\"{}\")", exception),
            Type::Return => "Type::Return".to_owned(),
        }
    }
}

impl Default for Type<'_> {
    fn default() -> Self {
        Self::Standard
    }
}

fn generate_children(children: &HashMap<char, Reference>, identifier: &str) -> String {
    let mut result = "|c| {
            match c {
                "
    .to_owned();

    for (c, reference) in children {
        result.push_str(&format!(
            "'{}' => Some({}),\n                ",
            c.escape_default(),
            reference.generate(identifier)
        ))
    }

    result.push_str(
        "_ => None,
            }
        }",
    );

    result
}

fn generate_subgraphs(subgraphs: &Vec<(Reference, Reference)>, identifier: &str) -> String {
    let mut result = "&[".to_owned();

    for (sub, ret) in subgraphs {
        result.push_str(&format!(
            "({}, {}),",
            sub.generate(identifier),
            ret.generate(identifier)
        ));
    }

    result.push_str("]");

    result
}

#[derive(Default, Debug)]
pub(crate) struct NodeGenerator<'a> {
    r#type: Type<'a>,
    children: HashMap<char, Reference>,
    alias_subgraphs: Vec<(Reference, Reference)>,
    grapheme_subgraphs: Vec<(Reference, Reference)>,
}

fn add_path_by_index<'a>(
    index: usize,
    word: &str,
    nodes: &mut Vec<NodeGenerator<'a>>,
    r#type: Type<'a>,
) {
    if word.is_empty() {
        let mut node = &mut nodes[index];
        if match node.r#type {
            Type::Standard => true,
            _ => false,
        } {
            node.r#type = r#type;
        }
        return;
    }

    let mut graphemes = word.graphemes(true);
    let grapheme = match graphemes.next() {
        Some(g) => g,
        None => unsafe {
            // SAFETY; We guaranteed above that `word` is non-empty, and therefore
            // `graphemes.next()` will always return a value.
            debug_unreachable!()
        },
    };
    if grapheme.chars().count() > 1 {
        let mut subgraph_node = NodeGenerator::default();
        let mut return_node = NodeGenerator::default();

        subgraph_node.add_path_ignoring_graphemes(grapheme, nodes, Type::Return);
        return_node.add_path(graphemes.as_str(), nodes, r#type);

        let nodes_len = nodes.len();
        nodes[index]
            .grapheme_subgraphs
            .push((Reference(nodes_len), Reference(nodes_len + 1)));
        nodes.push(subgraph_node);
        nodes.push(return_node);
    } else {
        let mut chars = word.chars();
        let c = match chars.next() {
            Some(c) => c,
            None => {
                unsafe {
                    // SAFETY; We guaranteed above that `word` is non-empty, and therefore
                    // `chars.next()` will always return a value.
                    debug_unreachable!()
                }
            }
        };
        let next_index = match nodes[index].children.get(&c) {
            Some(reference) => reference.0,
            None => {
                let nodes_len = nodes.len();
                nodes[index].children.insert(c, Reference(nodes_len));
                nodes.push(NodeGenerator::default());
                nodes_len
            }
        };
        add_path_by_index(next_index, chars.as_str(), nodes, r#type);
    }
}

fn add_path_by_index_ignoring_graphemes<'a>(
    index: usize,
    word: &str,
    nodes: &mut Vec<NodeGenerator<'a>>,
    r#type: Type<'a>,
) {
    if word.is_empty() {
        let mut node = &mut nodes[index];
        if match node.r#type {
            Type::Standard => true,
            _ => false,
        } {
            node.r#type = r#type;
        }
        return;
    }

    let mut chars = word.chars();
    let c = match chars.next() {
        Some(c) => c,
        None => {
            unsafe {
                // SAFETY; We guaranteed above that `word` is non-empty, and therefore
                // `chars.next()` will always return a value.
                debug_unreachable!()
            }
        }
    };
    let next_index = match nodes[index].children.get(&c) {
        Some(reference) => reference.0,
        None => {
            let nodes_len = nodes.len();
            nodes[index].children.insert(c, Reference(nodes_len));
            nodes.push(NodeGenerator::default());
            nodes_len
        }
    };
    add_path_by_index_ignoring_graphemes(next_index, chars.as_str(), nodes, r#type);
}

impl<'a> NodeGenerator<'a> {
    fn add_path(&mut self, word: &str, nodes: &mut Vec<NodeGenerator<'a>>, r#type: Type<'a>) {
        if word.is_empty() {
            if match self.r#type {
                Type::Standard => true,
                _ => false,
            } {
                self.r#type = r#type;
            }
            return;
        }

        let mut graphemes = word.graphemes(true);
        let grapheme = match graphemes.next() {
            Some(g) => g,
            None => unsafe {
                // SAFETY; We guaranteed above that `word` is non-empty, and therefore
                // `graphemes.next()` will always return a value.
                debug_unreachable!()
            },
        };
        if grapheme.chars().count() > 1 {
            let mut subgraph_node = NodeGenerator::default();
            let mut return_node = NodeGenerator::default();

            subgraph_node.add_path_ignoring_graphemes(grapheme, nodes, Type::Return);
            return_node.add_path(graphemes.as_str(), nodes, r#type);

            self.grapheme_subgraphs
                .push((Reference(nodes.len()), Reference(nodes.len() + 1)));
            nodes.push(subgraph_node);
            nodes.push(return_node);
        } else {
            let mut chars = word.chars();
            let index = self
                .children
                .entry(match chars.next() {
                    Some(c) => c,
                    None => {
                        unsafe {
                            // SAFETY; We guaranteed above that `word` is non-empty, and therefore
                            // `chars.next()` will always return a value.
                            debug_unreachable!()
                        }
                    }
                })
                .or_insert_with(|| {
                    nodes.push(NodeGenerator::default());
                    Reference(nodes.len() - 1)
                })
                .0;
            add_path_by_index(index, chars.as_str(), nodes, r#type);
        }
    }

    fn add_path_ignoring_graphemes(
        &mut self,
        word: &str,
        nodes: &mut Vec<NodeGenerator<'a>>,
        r#type: Type<'a>,
    ) {
        debug_assert!(!word.is_empty());

        let mut chars = word.chars();
        let index = self
            .children
            .entry(match chars.next() {
                Some(c) => c,
                None => {
                    unsafe {
                        // SAFETY; We guaranteed above that `word` is non-empty, and therefore
                        // `chars.next()` will always return a value.
                        debug_unreachable!()
                    }
                }
            })
            .or_insert_with(|| {
                nodes.push(NodeGenerator::default());
                Reference(nodes.len() - 1)
            })
            .0;
        add_path_by_index_ignoring_graphemes(index, chars.as_str(), nodes, r#type);
    }

    pub(crate) fn add_match(&mut self, word: &'a str, nodes: &mut Vec<NodeGenerator<'a>>) {
        self.add_path(word, nodes, Type::Match(word));
    }

    pub(crate) fn add_exception(&mut self, exception: &'a str, nodes: &mut Vec<NodeGenerator<'a>>) {
        self.add_path(exception, nodes, Type::Exception(exception));
    }

    pub(crate) fn add_return(&mut self, word: &str, nodes: &mut Vec<NodeGenerator<'a>>) {
        self.add_path(word, nodes, Type::Return);
    }

    fn consume_chars_until_return_node<'b>(
        &self,
        value: &'b str,
        nodes: &Vec<NodeGenerator<'a>>,
    ) -> Option<&'b str> {
        if let Type::Return = self.r#type {
            return Some(value);
        }

        if value.is_empty() {
            return None;
        }

        let mut chars = value.chars();
        self.children
            .get(&match chars.next() {
                Some(c) => c,
                None => unsafe {
                    // SAFETY: `value` is verified above to be non-empty. Therefore, `chars` will always
                    // return a value on `next()`.
                    debug_unreachable!()
                },
            })
            .and_then(|node_reference| {
                nodes[node_reference.0].consume_chars_until_return_node(chars.as_str(), nodes)
            })
    }

    fn find_alias_return_nodes(
        &self,
        value: &str,
        nodes: &Vec<NodeGenerator<'a>>,
    ) -> vec::IntoIter<usize> {
        if value.is_empty() {
            return vec![].into_iter();
        }

        let mut return_nodes = Vec::new();

        // Direct children.
        let mut chars = value.chars();
        self.children
            .get(&match chars.next() {
                Some(c) => c,
                None => unsafe {
                    // SAFETY: `value` is verified above to be non-empty. Therefore, `chars` will
                    // always return a value on `next()`.
                    debug_unreachable!()
                },
            })
            .into_iter()
            .for_each(|node_reference| {
                let remaining_value = chars.as_str();
                if remaining_value.is_empty() {
                    return_nodes.push(node_reference.0);
                } else {
                    return_nodes.extend(
                        nodes[node_reference.0].find_alias_return_nodes(remaining_value, nodes),
                    );
                }
            });

        // Grapheme subgraphs.
        for (grapheme_subgraph_reference, grapheme_return_reference) in &self.grapheme_subgraphs {
            nodes[grapheme_subgraph_reference.0]
                .consume_chars_until_return_node(value, nodes)
                .into_iter()
                .for_each(|consumed_value| {
                    if consumed_value.is_empty() {
                        return_nodes.push(grapheme_return_reference.0);
                    } else {
                        return_nodes.extend(
                            nodes[grapheme_return_reference.0]
                                .find_alias_return_nodes(consumed_value, nodes),
                        );
                    }
                });
        }

        return_nodes.into_iter()
    }

    pub(crate) fn add_alias(
        &mut self,
        value: &str,
        nodes: &mut Vec<NodeGenerator<'a>>,
        sub_graph_index: usize,
    ) {
        // Head recursion.
        for child_reference in self.children.values() {
            unsafe { (&mut nodes[child_reference.0] as *mut NodeGenerator).as_mut() }
                .unwrap()
                .add_alias(value, nodes, sub_graph_index);
        }

        for return_index in self.find_alias_return_nodes(value, nodes) {
            self.alias_subgraphs
                .push((Reference(sub_graph_index), Reference(return_index)));
        }
    }

    pub(crate) fn generate(&self, identifier: &str) -> String {
        format!(
            "::word_filter::node::Node {{
        r#type: ::word_filter::node::{},
        children: {},
        alias_subgraphs: {},
        grapheme_subgraphs: {},
    }}",
            self.r#type.generate(),
            generate_children(&self.children, identifier),
            generate_subgraphs(&self.alias_subgraphs, identifier),
            generate_subgraphs(&self.grapheme_subgraphs, identifier)
        )
    }
}
