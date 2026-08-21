//! Measures field-multiplication latency against throughput.

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use ff::Field;
use pasta_curves::{Fp, Fq};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

const MULTIPLICATIONS_PER_ITERATION: usize = 1_024;
const MAX_INDEPENDENT_CHAINS: usize = 8;
const RNG_SEED: [u8; 16] = [0x42; 16];

fn multiply_chains<F: Field, const CHAINS: usize>(
    mut accumulators: [F; CHAINS],
    factors: [F; CHAINS],
) -> [F; CHAINS] {
    debug_assert_eq!(MULTIPLICATIONS_PER_ITERATION % CHAINS, 0);

    for _ in 0..MULTIPLICATIONS_PER_ITERATION / CHAINS {
        for chain in 0..CHAINS {
            accumulators[chain] *= factors[chain];
        }
    }

    accumulators
}

fn bench_field<F: Field>(c: &mut Criterion, name: &str) {
    let mut rng = XorShiftRng::from_seed(RNG_SEED);
    let accumulators: [F; MAX_INDEPENDENT_CHAINS] = core::array::from_fn(|_| F::random(&mut rng));
    let factors: [F; MAX_INDEPENDENT_CHAINS] = core::array::from_fn(|_| F::random(&mut rng));

    let mut group = c.benchmark_group(format!("{name}/multiplication dependency"));
    group.throughput(Throughput::Elements(MULTIPLICATIONS_PER_ITERATION as u64));

    group.bench_function("1 chain", |b| {
        b.iter(|| {
            black_box(multiply_chains::<F, 1>(
                black_box([accumulators[0]]),
                black_box([factors[0]]),
            ))
        })
    });
    group.bench_function("2 independent chains", |b| {
        b.iter(|| {
            black_box(multiply_chains::<F, 2>(
                black_box([accumulators[0], accumulators[1]]),
                black_box([factors[0], factors[1]]),
            ))
        })
    });
    group.bench_function("4 independent chains", |b| {
        b.iter(|| {
            black_box(multiply_chains::<F, 4>(
                black_box([
                    accumulators[0],
                    accumulators[1],
                    accumulators[2],
                    accumulators[3],
                ]),
                black_box([factors[0], factors[1], factors[2], factors[3]]),
            ))
        })
    });
    group.bench_function("8 independent chains", |b| {
        b.iter(|| {
            black_box(multiply_chains::<F, 8>(
                black_box(accumulators),
                black_box(factors),
            ))
        })
    });

    group.finish();
}

fn criterion_benchmark(c: &mut Criterion) {
    bench_field::<Fp>(c, "Fp");
    bench_field::<Fq>(c, "Fq");
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
