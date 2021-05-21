use std::{
    env,
    fs::File,
    io::{BufWriter, Write},
    path::Path,
};
use word_filter_codegen::{Visibility, WordFilterGenerator};

fn main() {
    let file = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    let mut file = BufWriter::new(File::create(&file).unwrap());

    let mut base_generator = WordFilterGenerator::new();
    base_generator.visibility(Visibility::Pub);
    let mut foo_generator = base_generator.clone();
    foo_generator.word("foo");
    let mut bar_generator = base_generator.clone();
    bar_generator.word("bar");
    let mut grapheme_generator = base_generator.clone();
    grapheme_generator.word("bãr");

    writeln!(
        &mut file,
        "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
        foo_generator.generate("WORD"),
        foo_generator.clone().word("bar").generate("MULTIPLE_WORDS"),
        foo_generator
            .clone()
            .exception("foobar")
            .generate("EXCEPTION"),
        foo_generator
            .clone()
            .exceptions(&["afoo", "foob", "cfood"])
            .generate("MULTIPLE_EXCEPTIONS"),
        foo_generator.clone().separator(' ').generate("SEPARATOR"),
        bar_generator
            .clone()
            .separator(' ')
            .generate("BAR_SEPARATOR"),
        foo_generator.clone().alias('o', 'a').generate("ALIAS"),
        foo_generator
            .clone()
            .aliases(&[('o', 'a'), ('a', 'b')])
            .generate("ALIAS_ON_ALIAS"),
        bar_generator.clone().aliases(&[("b", "cd"),("a", "ef"), ("de", "g")]).generate("MERGED_ALIASES"),
        base_generator.clone().word("ahj").aliases(&[("a", "bc"), ("cdef", "g"), ("h", "de"), ("j", "fi")]).generate("MERGED_ALIASES_CONTIGUOUS"),
        bar_generator.clone().aliases(&[("b", "x"), ("a", "y"), ("r", "z"), ("xyz", "w")]).generate("MERGED_ALIASES_OVER_FULL_MATCH"),
        bar_generator.clone().aliases(&[('a', 'b'), ('b', 'a')]).generate("RECURSIVE_ALIASES"),
        foo_generator.clone().word("bar").alias('a', 'A').generate("MULTIPLE_WORDS_AND_ALIAS"),
        bar_generator.clone().separator(' ').alias('a', 'A').generate("SEPARATOR_AND_ALIAS"),
        bar_generator.clone().word("foobar").separator(' ').alias("bar", "baz").generate("WORD_IN_WORD_WITH_SEPARATOR_AND_ALIAS"),
        grapheme_generator.generate("GRAPHEME"),
        bar_generator.clone().alias('a', "ã").generate("GRAPHEME_IN_ALIAS"),
        grapheme_generator.clone().alias("ã", "õ").generate("ALIAS_ON_GRAPHEME"),
        base_generator.clone().word("ãbc").generate("GRAPHEME_AT_ROOT"),
    )
    .unwrap();
}
