use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use derivre::{RegexAst, RegexBuilder};
use std::hint::black_box;

fn check_match(divisor: u32, scale: u32) {
    let mut r = RegexBuilder::new();
    let id = r.mk(&RegexAst::MultipleOf(divisor, scale)).unwrap();
    let mut rx = r.to_regex(id);
    for mult in 1..=10 {
        let matching_int = mult * divisor;
        let matching_str = if scale == 0 {
            format!("{}", matching_int)
        } else {
            let scale_factor = 10u32.pow(scale);
            let integer_part = matching_int / scale_factor;
            let fractional_part = matching_int % scale_factor;
            format!(
                "{}.{:0>width$}",
                integer_part,
                fractional_part,
                width = scale as usize
            )
        };
        assert!(rx.is_match(&matching_str));
    }
}

fn matching_varying_divisor(c: &mut Criterion) {
    let mut group = c.benchmark_group("matching_varying_divisor");
    let scale = 3; // Fixed scale; adjust as needed

    let divisors = [2, 2_5, 2_25, 2_125, 2_0625, 2_03125, 2_015625];
    for &divisor in &divisors {
        group.bench_with_input(BenchmarkId::from_parameter(divisor), &divisor, |b, &d| {
            b.iter(|| check_match(d, black_box(scale)));
        });
    }

    group.finish();
}

fn matching_varying_scale(c: &mut Criterion) {
    let mut group = c.benchmark_group("matching_varying_scale");
    let divisor = 2_125; // Fixed divisor; adjust as needed

    let scales = [0, 1, 2, 3, 4, 5, 10];
    for &scale in &scales {
        group.bench_with_input(BenchmarkId::from_parameter(scale), &scale, |b, &s| {
            b.iter(|| check_match(black_box(divisor), s));
        });
    }

    group.finish();
}

fn match_varying_both(c: &mut Criterion) {
    let mut group = c.benchmark_group("match_varying_both");
    let divisors_and_scales = [
        (2, 0),
        (2_5, 1),
        (2_25, 2),
        (2_125, 3),
        (2_0625, 4),
        (2_03125, 5),
        (2_015625, 6),
    ];
    for (divisor, scale) in divisors_and_scales {
        group.throughput(Throughput::Elements(scale as u64));
        group.bench_with_input(
            BenchmarkId::new("divisor_and_scale", format!("{}-{}", divisor, scale)),
            &(divisor, scale),
            |b, &(d, s)| {
                b.iter(|| check_match(d, s));
            },
        );
    }

    group.finish();
}

criterion_group!(
    matching,
    matching_varying_divisor,
    matching_varying_scale,
    match_varying_both
);
criterion_main!(matching);
