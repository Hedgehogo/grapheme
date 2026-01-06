use criterion::{Bencher, Criterion, black_box, criterion_group, criterion_main};
use grapheme::prelude::*;
use unicode_normalization::UnicodeNormalization;

const INPUT: &str = include_str!("input.txt");
const INPUT_ASCII: &str = include_str!("input_ascii.txt");

fn normalize(s: String) -> String {
    s.nfd().collect()
}

fn eq_bench<E, O>(input: String, eq: E) -> impl FnMut(&mut Bencher<'_>)
where
    E: Fn(&Grapheme) -> O,
{
    move |b| {
        let graphemes = Graphemes::from_usvs(input.as_str());
        b.iter(|| {
            for c in graphemes.iter() {
                black_box(eq(c));
            }
        })
    }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut c_eq = c.benchmark_group("random_input");

    c_eq.bench_function(
        "unnormalized",
        eq_bench(INPUT.into(), |c| c.as_str().eq("a")),
    );
    c_eq.bench_function("nfd", eq_bench(INPUT.into(), |c| c.eq(g!('a'))));
    drop(c_eq);

    let mut c_eq_normalized = c.benchmark_group("eq_normalized");
    c_eq_normalized.bench_function(
        "unnormalized",
        eq_bench(normalize(INPUT.into()), |c| c.as_str().eq("a")),
    );
    c_eq_normalized.bench_function("nfd", eq_bench(normalize(INPUT.into()), |c| c.eq(g!('a'))));
    drop(c_eq_normalized);

    let mut c_eq_ascii = c.benchmark_group("eq_ascii");
    c_eq_ascii.bench_function(
        "unnormalized",
        eq_bench(INPUT_ASCII.into(), |c| c.as_str().eq("a")),
    );
    c_eq_ascii.bench_function("nfd", eq_bench(INPUT_ASCII.into(), |c| c.eq(g!('a'))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
