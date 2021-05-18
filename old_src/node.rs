#[derive(Debug)]
pub enum Type<'a> {
    Standard,
    Match(&'a str),
    Exception(&'a str),
    Return,
}

#[derive(Debug)]
pub struct Node<'a> {
    pub r#type: Type<'a>,
    pub children: fn(char) -> &'a Node<'a>,
    pub alias_subgraphs: &'a [(&'a Node<'a>, &'a Node<'a>)],
    pub grapheme_subgraphs: &'a [(&'a Node<'a>, &'a Node<'a>)],
}
