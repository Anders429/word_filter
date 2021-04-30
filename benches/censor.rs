#[cfg(feature = "criterion")]
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use csv::Reader;
use word_filter::WordFilterBuilder;

#[cfg(feature = "criterion")]
fn builder_benchmark(c: &mut Criterion) {
    c.bench_function("censor", |b| {
        let filter = WordFilterBuilder::new()
            .words(Reader::from_path("benches/data/words.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string()))
            .exceptions(Reader::from_path("benches/data/exceptions.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string()))
            .words(Reader::from_path("benches/data/separators.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string()))
            .aliases(
                Reader::from_path("benches/data/alias_sources.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string())
                    .zip(Reader::from_path("benches/data/aliases.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string()))
                    .collect::<Vec<_>>()
                    .as_slice(),
            )
            .build();

        b.iter(|| {
            black_box(filter.censor(black_box(include_str!("data/input.txt"))));
        })
    });
}

#[cfg(feature = "criterion")]
criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(100);
    targets = builder_benchmark
}
#[cfg(feature = "criterion")]
criterion_main!(benches);

#[cfg(not(feature = "criterion"))]
fn main() {}
