#[macro_use]
extern crate criterion;

use criterion::{black_box, BatchSize, BenchmarkId, Criterion, Throughput};
use group::ff::Field;
use halo2_proofs::pasta::Fp;
use halo2_proofs::plonk::deferred_bench as evaluation_bench;
use halo2_proofs::poly::multiopen::deferred_bench as multiopen_bench;
use halo2_proofs::poly::{deferred_bench as evaluator_bench, Coeff, Polynomial};

const SMALL_SIZES: [usize; 6] = [1, 2, 4, 8, 16, 64];
const ORCHARD_EVALUATION_SIZE: usize = 1 << 11;
const ORCHARD_POWER_LANES: usize = 1 << 12;
const ORCHARD_POWER_PRODUCTS: [usize; 8] = [1, 2, 3, 4, 5, 7, 8, 25];
const ORCHARD_MULTI_COEFFICIENTS: usize = 1 << 11;
const ORCHARD_MULTI_PRODUCTS: [usize; 4] = [2, 4, 8, 49];

fn values(len: usize, offset: u64) -> Vec<Fp> {
    (0..len)
        .map(|index| Fp::from(offset + index as u64 + 1))
        .collect()
}

fn bench_deferred_inner_product(c: &mut Criterion) {
    let mut group = c.benchmark_group("deferred_inner_product");
    for len in SMALL_SIZES
        .into_iter()
        .chain(std::iter::once(ORCHARD_EVALUATION_SIZE))
    {
        let polynomial = values(len, 0);
        let powers = values(len, 10_000);
        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::from_parameter(len), &len, |b, _| {
            b.iter(|| {
                black_box(evaluation_bench::inner_product(
                    black_box(&polynomial),
                    black_box(&powers),
                ))
            })
        });
    }
    group.finish();
}

fn bench_power_fold(c: &mut Criterion) {
    let mut group = c.benchmark_group("power_fold");
    for (lanes, products, label) in [
        (8, SMALL_SIZES.as_slice(), "small"),
        (
            ORCHARD_POWER_LANES,
            ORCHARD_POWER_PRODUCTS.as_slice(),
            "orchard",
        ),
    ] {
        for &product_count in products {
            let terms = (0..product_count)
                .map(|product| values(lanes, product as u64 * 10_000))
                .collect::<Vec<_>>();
            let powers = values(product_count, 20_000);
            group.throughput(Throughput::Elements((lanes * product_count) as u64));
            group.bench_with_input(
                BenchmarkId::new(label, product_count),
                &(lanes, product_count),
                |b, _| {
                    b.iter_batched(
                        || vec![Fp::ZERO; lanes],
                        |mut output| {
                            evaluator_bench::power_fold(
                                black_box(&terms),
                                black_box(&powers),
                                black_box(&mut output),
                            );
                            black_box(output);
                        },
                        BatchSize::SmallInput,
                    )
                },
            );
        }
    }
    group.finish();
}

fn bench_multiopen_fold(c: &mut Criterion) {
    let mut group = c.benchmark_group("multiopen_fold");
    for (coefficients, product_counts, label) in [
        (8, SMALL_SIZES.as_slice(), "small"),
        (
            ORCHARD_MULTI_COEFFICIENTS,
            ORCHARD_MULTI_PRODUCTS.as_slice(),
            "orchard",
        ),
    ] {
        for &product_count in product_counts {
            let polynomial_count = product_count + 1;
            let polynomials = (0..polynomial_count)
                .map(|polynomial| {
                    Polynomial::<Fp, Coeff>::from_values(values(
                        coefficients,
                        polynomial as u64 * 10_000,
                    ))
                })
                .collect::<Vec<_>>();
            let powers = values(polynomial_count, 20_000);
            group.throughput(Throughput::Elements((coefficients * product_count) as u64));
            group.bench_with_input(
                BenchmarkId::new(label, product_count),
                &(coefficients, product_count),
                |b, _| {
                    b.iter_batched(
                        || vec![Fp::ZERO; coefficients],
                        |mut output| {
                            multiopen_bench::multiopen_fold(
                                black_box(&mut output),
                                black_box(&polynomials),
                                black_box(&powers),
                            );
                            black_box(output);
                        },
                        BatchSize::SmallInput,
                    )
                },
            );
        }
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_deferred_inner_product,
    bench_power_fold,
    bench_multiopen_fold
);
criterion_main!(benches);
