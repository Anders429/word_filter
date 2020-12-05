enum Node<'a> {
    // Default node. All Character nodes implicitly point to None by default.
    None,
    Character(std::collections::HashMap<char, Vec<Node<'a>>>),
    Match(&'a str),
    Exception(&'a str),

    // <subgraph_node, return_node>.
    SubGraph(&'a Node<'a>, &'a Node<'a>),
    Return,
}

impl PartialEq for Node<'_> {
    fn eq(&self, other: &Self) -> bool {
        if std::mem::discriminant(self) == std::mem::discriminant(other) {
            match self {
                Node::Match(s) => {
                    if let Node::Match(t) = other {
                        s == t
                    } else {
                        false
                    }
                }
                Node::Exception(s) => {
                    if let Node::Exception(t) = other {
                        s == t
                    } else {
                        false
                    }
                }
                Node::SubGraph(node_0, ret_0) => {
                    if let Node::SubGraph(node_1, ret_1) = other {
                        std::ptr::eq(node_0, node_1) && std::ptr::eq(ret_0, ret_1)
                    } else {
                        false
                    }
                }
                // The default case. None and Return follow trivially. For Character, it is
                // defined that the existence of a Character is its defining trait, and further
                // Nodes it is mapped to do not alter its value. In other words, each edge will
                // only point to one unique Character Node.
                _ => true,
            }
        } else {
            false
        }
    }
}

impl<'a> Node<'a> {
    fn add(&mut self, edge: char, node: Node<'a>) -> &mut Node<'a> {
        if let Node::Character(map) = self {
            let nodes = map.entry(edge).or_insert_with(Vec::new);
            let i = nodes
                .iter()
                .position(|existing_node| node == *existing_node)
                .unwrap_or_else(|| {
                    nodes.push(node);
                    nodes.len() - 1
                });
            &mut nodes[i]
        } else {
            self
        }
    }

    fn add_match(&mut self, word: &'a str) {
        let mut char_indices = word.char_indices();
        if let Some((_current_index, current)) = char_indices.next() {
            if let Some((next_index, _next)) = char_indices.next() {
                self.add(current, Node::Character(std::collections::HashMap::new()))
                    .add_match(&word[next_index..]);
            } else {
                self.add(current, Node::Match(word));
            }
        }
    }

    fn add_exception(&mut self, word: &'a str) {
        let mut char_indices = word.char_indices();
        if let Some((_current_index, current)) = char_indices.next() {
            if let Some((next_index, _next)) = char_indices.next() {
                self.add(current, Node::Character(std::collections::HashMap::new()))
                    .add_exception(&word[next_index..]);
            } else {
                self.add(current, Node::Exception(word));
            }
        }
    }
    
    fn find_alias_return_node(&self, value: &str) -> Option<&[&Node]> {
        if self == Node::None {
            return None;
        }
        if value.is_empty() {
            return Some(self);
        }
        let char_indices = value.char_indices();
        let c = char_indices.next().map(|_, c| c).unwrap();
        let nodes = self.traverse(c);
        
        
        
        for node in nodes {
            let offset = char_indices.next().map(|offset, _| offset).unwrap_or(value.len());
            node.find_alias_return_node(value[offset..]);
        }
    }

    fn add_alias(&mut self, value: &str, alias_sub_graph: &Node<'a>) {
        if let Node::Character(map) = self {
            // DFS to find aliases.
            // TODO: Try recursion instead? That will help with "borrowing" issues.
            let stack = map.iter().fold(Vec::new(), |accumulator, (c, nodes)| {
                for node in nodes {
                    accumulator.push(("".to_string(), node, node));
                    if value.starts_with(*c) {
                        accumulator.push((c.to_string(), self, node))
                    }
                }
                accumulator
            });
        }
    }

    fn add_return(&mut self, word: &str) {
        let mut char_indices = word.char_indices();
        if let Some((_current_index, current)) = char_indices.next() {
            if let Some((next_index, _next)) = char_indices.next() {
                self.add(current, Node::Character(std::collections::HashMap::new()))
                    .add_return(&word[next_index..]);
            } else {
                self.add(current, Node::Return);
            }
        }
    }

    fn traverse(&self, edge: &char) -> &[&Node] {
        match self {
            Node::Character(map) => match map.get(edge) {
                Some(nodes) => nodes,
                None => &[&Node::None],
            },
            _ => &[&Node::None],
        }
    }
}

pub struct Options {}

pub struct WordFilter<'a> {
    root: Node<'a>,
    separators_root: Node<'a>,
    aliases_roots: std::collections::HashMap<char, Node<'a>>,
    options: Options,
}

impl<'a> WordFilter<'a> {
    pub fn new(
        filtered_words: &[&'a str],
        exceptions: &[&'a str],
        separators: &[&str],
        aliases: &[(&str, &str)],
        options: Options,
    ) -> Self {
        let mut root = Node::Character(std::collections::HashMap::new());
        for filtered_word in filtered_words {
            root.add_match(filtered_word);
        }
        for exception in exceptions {
            root.add_exception(exception);
        }

        let mut separators_root = Node::Character(std::collections::HashMap::new());
        for separator in separators {
            separators_root.add_return(separator);
        }

        let mut aliases_roots = std::collections::HashMap::new();
        for alias in aliases {}

        Self {
            root,
            separators_root,
            aliases_roots,
            options,
        }
    }
}
