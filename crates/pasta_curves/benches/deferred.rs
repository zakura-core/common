#[cfg(target_arch = "aarch64")]
use criterion::BatchSize;
use criterion::{BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main};
use pasta_curves::{Fp, Fq, deferred::DeferredField};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

const SEED: [u8; 16] = [
    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
];

fn benchmark_field<F: DeferredField>(criterion: &mut Criterion, field_name: &str) {
    let mut group = criterion.benchmark_group(format!("{field_name}/deferred-inner-product"));
    let mut rng = XorShiftRng::from_seed(SEED);

    for len in [4_usize, 16, 64, 2_048] {
        let lhs = (0..len).map(|_| F::random(&mut rng)).collect::<Vec<_>>();
        let rhs = (0..len).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

        group.throughput(Throughput::Elements(len as u64));
        group.bench_with_input(BenchmarkId::new("scalar", len), &len, |bencher, _| {
            bencher.iter(|| {
                let mut accumulator = F::Accumulator::default();
                for (lhs, rhs) in lhs.iter().zip(&rhs) {
                    F::mul_accumulate(&mut accumulator, black_box(lhs), black_box(rhs));
                }
                black_box(F::reduce(accumulator))
            });
        });
        #[cfg(target_arch = "aarch64")]
        group.bench_with_input(BenchmarkId::new("bulk", len), &len, |bencher, _| {
            bencher.iter(|| F::inner_product(black_box(&lhs), black_box(&rhs)));
        });
    }

    group.finish();

    #[cfg(target_arch = "aarch64")]
    {
        let mut group = criterion.benchmark_group(format!("{field_name}/deferred-weighted-sum"));
        for len in [4_usize, 16, 64, 2_048] {
            let lhs = (0..len).map(|_| F::random(&mut rng)).collect::<Vec<_>>();
            let rhs = (0..len).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

            group.throughput(Throughput::Elements(len as u64));
            group.bench_with_input(
                BenchmarkId::new("scalar-products", len),
                &len,
                |bencher, _| {
                    bencher.iter_batched(
                        || vec![F::Accumulator::default(); len],
                        |mut accumulators| {
                            for ((accumulator, lhs), rhs) in
                                accumulators.iter_mut().zip(&lhs).zip(&rhs)
                            {
                                F::mul_accumulate(accumulator, black_box(lhs), black_box(rhs));
                            }
                            black_box(accumulators)
                        },
                        BatchSize::SmallInput,
                    );
                },
            );
            group.bench_with_input(
                BenchmarkId::new("bulk-products", len),
                &len,
                |bencher, _| {
                    bencher.iter_batched(
                        || vec![F::Accumulator::default(); len],
                        |mut accumulators| {
                            F::weighted_sum(&mut accumulators, black_box(&lhs), black_box(&rhs));
                            black_box(accumulators)
                        },
                        BatchSize::SmallInput,
                    );
                },
            );
            group.bench_with_input(
                BenchmarkId::new("scalar-broadcast", len),
                &len,
                |bencher, _| {
                    bencher.iter_batched(
                        || vec![F::Accumulator::default(); len],
                        |mut accumulators| {
                            for (accumulator, lhs) in accumulators.iter_mut().zip(&lhs) {
                                F::mul_accumulate(accumulator, black_box(lhs), black_box(&rhs[0]));
                            }
                            black_box(accumulators)
                        },
                        BatchSize::SmallInput,
                    );
                },
            );
            group.bench_with_input(
                BenchmarkId::new("bulk-broadcast", len),
                &len,
                |bencher, _| {
                    bencher.iter_batched(
                        || vec![F::Accumulator::default(); len],
                        |mut accumulators| {
                            F::weighted_sum(
                                &mut accumulators,
                                black_box(&lhs),
                                black_box(&rhs[..1]),
                            );
                            black_box(accumulators)
                        },
                        BatchSize::SmallInput,
                    );
                },
            );
        }
        group.finish();
    }
}

fn benchmark_deferred(criterion: &mut Criterion) {
    benchmark_field::<Fp>(criterion, "Fp");
    benchmark_field::<Fq>(criterion, "Fq");
}

criterion_group!(benches, benchmark_deferred);
criterion_main!(benches);
