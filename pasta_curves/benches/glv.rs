//! Benchmarks for GLV scalar multiplication.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use ff::Field;
use pasta_curves::glv::{Decomposed, GlvParams, Table};
use pasta_curves::{pallas, vesta};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

// Sizes bracketing the halo2 proving workloads (Orchard's k = 11 circuit
// commits at 2^11..2^13); the backend planner switches representations
// across this range.
const MULTIEXP_SIZES: [usize; 5] = [1 << 9, 1 << 10, 1 << 11, 1 << 12, 1 << 13];

// A k = 13 Halo generator collapse calls batches from 2^12 down to 2^0.
const SAME_SCALAR_BATCH_SIZES: [usize; 13] =
    [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096];
const SAME_SCALAR_CORPUS_SIZE: usize = 8;

fn same_scalar_corpus<C: GlvParams>() -> Vec<C::ScalarExt> {
    let mut rng = XorShiftRng::from_seed([0x42; 16]);
    (0..SAME_SCALAR_CORPUS_SIZE)
        .map(|_| C::ScalarExt::random(&mut rng))
        .collect()
}

fn criterion_benchmark(c: &mut Criterion) {
    glv_bench::<pallas::Point>(c, "Pallas");
    glv_bench::<vesta::Point>(c, "Vesta");
}

fn glv_bench<C: GlvParams>(c: &mut Criterion, name: &str) {
    let mut group = c.benchmark_group(name);

    // Deterministic full-width setup (matches the crate's other benches).
    let k = (C::ScalarExt::from(0x9E37_79B9_7F4A_7C15u64).square()
        + C::ScalarExt::from(0x0123_4567_89AB_CDEFu64))
    .square();
    let p = C::generator() * (k + C::ScalarExt::ONE);
    let points: Vec<C> = (1..=50)
        .map(|i| C::generator() * (k + C::ScalarExt::from(i)))
        .collect();
    let table = Table::new(&p);
    let decomposed = Decomposed::<C>::new(&k);

    group.bench_function("native mul", |b| b.iter(|| p * k));
    group.bench_function("mul_glv one-shot", |b| b.iter(|| p.mul_glv(&k)));
    group.bench_function("table build (solo)", |b| b.iter(|| Table::new(&p)));
    // Whole-batch time; divide by 50 to compare per-point cost with the
    // solo build.
    group.bench_function("table build (batch of 50)", |b| {
        b.iter(|| Table::batch(&points));
    });
    group.bench_function("table mul (reused table)", |b| b.iter(|| table.mul(&k)));
    group.bench_function("table mul (reused table + decomposed)", |b| {
        b.iter(|| table.mul_decomposed(&decomposed));
    });
    // The per-scalar hoisted work on its own (GLV split + joint recoding).
    group.bench_function("decompose + recode", |b| {
        b.iter(|| Decomposed::<C>::new(&k))
    });

    group.finish();

    let mut group = c.benchmark_group(format!("{name}/same-scalar batch"));
    group.sample_size(10);
    // This measures the multiplication kernel. The caller's addition and
    // final batch normalization are common to both implementations.
    let scalars = same_scalar_corpus::<C>();
    for size in SAME_SCALAR_BATCH_SIZES {
        group.throughput(Throughput::Elements((size * scalars.len()) as u64));
        let points: Vec<C::AffineExt> = (0..size)
            .map(|i| C::AffineExt::from(C::generator() * (k + C::ScalarExt::from(i as u64 + 1))))
            .collect();
        let mut output = vec![C::identity(); size];

        group.bench_with_input(BenchmarkId::new("native loop", size), &size, |b, _| {
            b.iter(|| {
                let points = black_box(points.as_slice());
                let scalars = black_box(scalars.as_slice());
                for scalar in scalars {
                    for (point, output) in points.iter().zip(output.iter_mut()) {
                        *output = *point * scalar;
                    }
                    black_box(output.as_slice());
                }
            });
        });
        group.bench_with_input(BenchmarkId::new("batch hook", size), &size, |b, _| {
            b.iter(|| {
                let points = black_box(points.as_slice());
                let scalars = black_box(scalars.as_slice());
                for scalar in scalars {
                    C::batch_mul_same_scalar_vartime(points, scalar, &mut output);
                    black_box(output.as_slice());
                }
            });
        });
    }
    group.finish();

    // The arbitrary-scalar MSM through the public planner entry point
    // (Signed-Booth or Eisenstein-orbit buckets, as the cost model picks
    // for the current size and thread pool).
    let mut group = c.benchmark_group(format!("{name}/multiexp"));
    group.sample_size(10);
    for size in MULTIEXP_SIZES {
        group.throughput(Throughput::Elements(size as u64));
        let mut rng = XorShiftRng::from_seed([0x42; 16]);
        let msm_scalars: Vec<C::ScalarExt> =
            (0..size).map(|_| C::ScalarExt::random(&mut rng)).collect();
        let msm_bases: Vec<C::AffineExt> = (0..size)
            .map(|i| (C::generator() * (k + C::ScalarExt::from(i as u64 + 1))).to_affine())
            .collect();

        group.bench_with_input(
            BenchmarkId::new("try_multiexp_vartime", size),
            &size,
            |b, _| {
                b.iter(|| {
                    C::try_multiexp_vartime(
                        black_box(msm_scalars.as_slice()),
                        black_box(msm_bases.as_slice()),
                    )
                    .expect("the planner selects a GLV backend at these sizes")
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
