use std::{
    env,
    fs::File,
    io::{BufWriter, Write},
    path::Path,
};
use word_filter_codegen::WordFilterGenerator;

fn main() {
    let file = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    let mut file = BufWriter::new(File::create(&file).unwrap());

    writeln!(
        &mut file,
        "{}",
        WordFilterGenerator::new()
            .word("foo")
            .exception("foobar")
            .separator(" ")
            .alias("f", "F")
            .generate("FILTER")
    );
}
