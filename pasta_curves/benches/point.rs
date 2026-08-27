//! Benchmarks for point operations.

use criterion::{criterion_group, criterion_main, Criterion};

use ff::Field;
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::{pallas, vesta};

fn criterion_benchmark(c: &mut Criterion) {
    point_bench::<pallas::Point>(c, "Pallas");
    point_bench::<vesta::Point>(c, "Vesta");
}

fn point_bench<C>(c: &mut Criterion, name: &str)
where
    C: CurveExt,
    for<'a, 'b> &'a C: core::ops::Add<&'b C::AffineExt, Output = C>,
{
    let mut group = c.benchmark_group(name);

    let a = C::generator();
    let b = a.double();
    let a_affine = a.to_affine();
    let b_affine = b.to_affine();
    let scalar = (C::ScalarExt::from(0x9e37_79b9_7f4a_7c15).square()
        + C::ScalarExt::from(0x0123_4567_89ab_cdef))
    .square();

    group.bench_function("point doubling", |bencher| bencher.iter(|| a.double()));

    group.bench_function("point addition", |bencher| bencher.iter(|| a + b));

    group.bench_function("point mixed addition", |bencher| {
        bencher.iter(|| &a + &b_affine)
    });

    group.bench_function("affine addition", |bencher| {
        bencher.iter(|| a_affine + b_affine)
    });

    group.bench_function("point subtraction", |bencher| bencher.iter(|| a - b));

    group.bench_function("point scalar multiplication", |bencher| {
        bencher.iter(|| a * scalar)
    });

    group.bench_function("point to_bytes", |bencher| bencher.iter(|| a.to_bytes()));

    let repr = a.to_bytes();
    group.bench_function("point from_bytes", |bencher| {
        bencher.iter(|| C::from_bytes(&repr))
    });

    group.bench_function("point to_affine", |bencher| bencher.iter(|| a.to_affine()));

    for &n in [100, 1000, 10000].iter() {
        let input = vec![a; n];
        let mut output = vec![C::Affine::default(); n];
        group.bench_function(format!("point batch_normalize/{}", n), |bencher| {
            bencher.iter(|| C::batch_normalize(input.as_slice(), output.as_mut_slice()));
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
