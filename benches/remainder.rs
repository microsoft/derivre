use criterion::{
    criterion_group, criterion_main, AxisScale, BenchmarkId, Criterion, PlotConfiguration,
    Throughput,
};
use derivre::{RegexAst, RegexBuilder};
use std::hint::black_box;

fn check_match(divisor: u32, scale: u32) {
    let mut r = RegexBuilder::new();
    let id = r.mk(&RegexAst::MultipleOf(divisor, scale)).unwrap();
    let mut rx = r.to_regex(id);
    for mult in 0..=10 {
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
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("matching_varying_divisor");
    group.plot_config(plot_config);

    let divisors = [2_5, 2_25, 2_125, 2_0625, 2_03125, 2_015625];
    let scales = [1, 2, 3, 4, 5, 10];
    for &divisor in &divisors {
        for &scale in &scales {
            group.bench_with_input(
                BenchmarkId::new(format!("scale={}", scale), divisor),
                &divisor,
                |b, &d| {
                    b.iter(|| check_match(d, black_box(scale)));
                },
            );
        }
    }

    group.finish();
}

fn matching_varying_scale(c: &mut Criterion) {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("matching_varying_scale");
    group.plot_config(plot_config);

    let divisors = [2_5, 2_25, 2_125, 2_0625, 2_03125, 2_015625];
    let scales = [1, 2, 3, 4, 5, 10];
    for &scale in &scales {
        for &divisor in &divisors {
            group.bench_with_input(
                BenchmarkId::new(format!("divisor={}", divisor), scale),
                &scale,
                |b, &s| {
                    b.iter(|| check_match(black_box(divisor), s));
                },
            );
        }
    }

    group.finish();
}

fn match_varying_both(c: &mut Criterion) {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("match_varying_both");
    group.plot_config(plot_config);

    let divisors_and_scales = [
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
