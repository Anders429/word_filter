#[cfg(feature = "criterion")]
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use word_filter::WordFilterBuilder;

#[cfg(feature = "criterion")]
fn builder_benchmark(c: &mut Criterion) {
    c.bench_function("censor", |b| {
        let filter = WordFilterBuilder::new()
            .word(black_box("foo"))
            .exception(black_box("foobar"))
            .separator(black_box(" "))
            .alias(black_box("f"), black_box("F"))
            .build();

        b.iter(|| {
            black_box(filter.censor(black_box("This is test input. It might contain foo, or it might contain foobar, or it might contain nothing.")));
        })
    });
}

#[cfg(feature = "criterion")]
criterion_group!(benches, builder_benchmark);
#[cfg(feature = "criterion")]
criterion_main!(benches);

#[cfg(not(feature = "criterion"))]
fn main() {}
