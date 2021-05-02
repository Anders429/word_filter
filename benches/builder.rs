#[cfg(feature = "benchmarks")]
use criterion::{criterion_group, criterion_main, Criterion};
#[cfg(feature = "benchmarks")]
use csv::Reader;
use word_filter::WordFilterBuilder;

#[cfg(feature = "benchmarks")]
fn builder_benchmark(c: &mut Criterion) {
    c.bench_function("construction", |b| {
        b.iter(|| {
            WordFilterBuilder::new()
                .words(Reader::from_path("benches/data/words.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string()))
                .exceptions(Reader::from_path("benches/data/exceptions.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string()))
                .words(Reader::from_path("benches/data/separators.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string()))
                .aliases(
                    Reader::from_path("benches/data/alias_sources.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string())
                        .zip(Reader::from_path("benches/data/aliases.csv").unwrap().records().map(|r| r.unwrap().as_slice().to_string()))
                        .collect::<Vec<_>>()
                        .as_slice(),
                )
                .build()
        })
    });
}

#[cfg(feature = "benchmarks")]
criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(100);
    targets = builder_benchmark
}
#[cfg(feature = "benchmarks")]
criterion_main!(benches);

#[cfg(not(feature = "benchmarks"))]
fn main() {}
