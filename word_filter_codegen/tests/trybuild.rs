use std::{
    env,
    fs::File,
    io::{BufWriter, Write},
};
use word_filter_codegen::{Visibility, WordFilterGenerator};

macro_rules! compiles {
    ($test_name:ident, $generator:expr) => {
        #[test]
        fn $test_name() {
            let path = concat!(env!("OUT_DIR"), stringify!($test_name), ".rs");
            let mut file = BufWriter::new(File::create(&path).unwrap());
        
            writeln!(&mut file, "mod this{{\n{}\n}}\n\nfn main() {{}}", $generator.generate("TEST")).unwrap();
            // Flush the buffer before the file is attempted to be built.
            drop(file);
            
            trybuild::TestCases::new().pass(path);
        }
    }
}

compiles!(private_visibility, WordFilterGenerator::new().visibility(Visibility::Private));
compiles!(public_visibility, WordFilterGenerator::new().visibility(Visibility::Pub));
compiles!(crate_visibility, WordFilterGenerator::new().visibility(Visibility::PubCrate));
compiles!(self_visibility, WordFilterGenerator::new().visibility(Visibility::PubIn("self".to_owned())));
compiles!(super_visibility, WordFilterGenerator::new().visibility(Visibility::PubIn("super".to_owned())));
compiles!(path_visibility, WordFilterGenerator::new().visibility(Visibility::PubIn("crate::this".to_owned())));
compiles!(word, WordFilterGenerator::new().word("foo"));
compiles!(words, WordFilterGenerator::new().words(&["foo", "bar"]));
compiles!(exception, WordFilterGenerator::new().exception("foo"));
compiles!(exceptions, WordFilterGenerator::new().exceptions(&["foo", "bar"]));
compiles!(separator, WordFilterGenerator::new().separator("foo"));
compiles!(separators, WordFilterGenerator::new().separators(&["foo", "bar"]));
compiles!(alias, WordFilterGenerator::new().alias("foo", "bar"));
compiles!(aliases, WordFilterGenerator::new().aliases(&[("foo", "bar"), ("baz", "qux")]));
compiles!(graphemes, WordFilterGenerator::new().word("bãr"));
compiles!(null_character, WordFilterGenerator::new().word("\0fo\0o"));
compiles!(alias_on_word, WordFilterGenerator::new().word("foo").alias('o', 'a'));
compiles!(alias_on_exception, WordFilterGenerator::new().exception("foo").alias('o', 'a'));
compiles!(empty, WordFilterGenerator::new().word(""));
compiles!(grapheme_alias, WordFilterGenerator::new().word("bãr").alias("ã", "õ"));
compiles!(grapheme_at_start, WordFilterGenerator::new().word("ãbc"));
compiles!(grapheme_alias_not_applied, WordFilterGenerator::new().word("bar").alias("ã", "õ"));
compiles!(long_grapheme_alias, WordFilterGenerator::new().word("bãr").alias("ãr", "õr"));
compiles!(empty_alias, WordFilterGenerator::new().alias("", ""));
compiles!(alias_not_applied_on_longer_grapheme, WordFilterGenerator::new().word("bã̃r").alias("ã", "õ"));
compiles!(merged_aliases, WordFilterGenerator::new().aliases(&[("b", "cd"),("a", "ef"), ("de", "g")]));
