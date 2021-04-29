#[cfg(feature = "criterion")]
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use word_filter::WordFilterBuilder;

#[cfg(feature = "criterion")]
fn builder_benchmark(c: &mut Criterion) {
    c.bench_function("construction", |b| {
        b.iter(|| {
            WordFilterBuilder::new()
                .word(black_box("foo"))
                .exception(black_box("foobar"))
                .separator(black_box(" "))
                .alias(black_box("f"), black_box("F"))
                .build()
        })
    });
}

#[cfg(feature = "criterion")]
criterion_group!(benches, builder_benchmark);
#[cfg(feature = "criterion")]
criterion_main!(benches);

#[cfg(not(feature = "criterion"))]
fn main () {}
