use criterion::{Bencher, Criterion, black_box, criterion_group, criterion_main};
use grapheme::{normalization::Normalization, prelude::*};
use unicode_normalization::UnicodeNormalization;

const INPUT: &str = include_str!("input.txt");
const INPUT_ASCII: &str = include_str!("input_ascii.txt");

struct GsNfd(String);

impl GsNfd {
    #[inline]
    fn as_gs(&self) -> &Graphemes<Nfd> {
        unsafe { Graphemes::from_usvs_unchecked(&self.0) }
    }
}

#[inline]
fn normalize(s: &str) -> GsNfd {
    GsNfd(s.nfd().collect())
}

fn eq_bench<E, O, N: Normalization>(input: &Graphemes<N>, eq: E) -> impl FnMut(&mut Bencher<'_>)
where
    E: Fn(&Grapheme<N>) -> O,
{
    move |b| {
        let graphemes = input;
        b.iter(|| {
            for c in graphemes.iter() {
                black_box(eq(c));
            }
        })
    }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut c_eq = c.benchmark_group("eq_rnd_inp");

    c_eq.bench_function("byte", eq_bench(INPUT.into(), |c| c.as_str().eq("a")));
    c_eq.bench_function("nfd", eq_bench(INPUT.into(), |c| c.eq(g!('a'))));
    drop(c_eq);

    let mut c_eq_normalized = c.benchmark_group("eq_nfd_inp");
    c_eq_normalized.bench_function(
        "byte",
        eq_bench(normalize(INPUT).as_gs().as_unnormalized(), |c| {
            c.as_str().eq("a")
        }),
    );
    c_eq_normalized.bench_function(
        "nfd",
        eq_bench(normalize(INPUT).as_gs().as_unnormalized(), |c| {
            c.eq(g!('a'))
        }),
    );
    c_eq_normalized.bench_function(
        "nfd_typed",
        eq_bench(normalize(INPUT).as_gs(), |c| c.eq(g!('a'd))),
    );
    drop(c_eq_normalized);

    let mut c_eq_ascii = c.benchmark_group("eq_ascii_inp");
    c_eq_ascii.bench_function("byte", eq_bench(INPUT_ASCII.into(), |c| c.as_str().eq("a")));
    c_eq_ascii.bench_function("nfd", eq_bench(INPUT_ASCII.into(), |c| c.eq(g!('a'))));
    drop(c_eq_ascii);

    let mut c_nfd = c.benchmark_group("nfd_rnd_inp");
    c_nfd.bench_function("on_the_fly", |b| {
        b.iter(|| {
            let graphemes: &Graphemes = black_box(INPUT.into());
            for c in graphemes.iter() {
                black_box(c.eq(g!('a')));
            }
        })
    });
    c_nfd.bench_function("prenormalize", |b| {
        b.iter(|| {
            let graphemes = normalize(black_box(INPUT.into()));
            let graphemes = graphemes.as_gs();
            for c in graphemes.iter() {
                black_box(c.eq(g!('a'd)));
            }
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
