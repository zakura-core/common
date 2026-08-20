//! Compares K-accumulator ("K-lane") Montgomery batch inversion at various
//! batch sizes.
//!
//! The single-lane algorithm's forward prefix products and backward
//! accumulator walk are serial multiplication chains, so they run at the
//! field multiplication's dependency latency. K lanes split the values into
//! K interleaved groups with independent chains (throughput-bound), at a
//! fixed cost of 3(K-1) extra multiplications per batch: K-1 to join the
//! group products before the single shared inversion, and a
//! mini-back-substitution over the K group products after it.

use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};
use ff::Field;
use pasta_curves::Fp;
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

/// K-lane Montgomery batch inversion of nonzero values. K = 1 is the
/// classic single-chain algorithm; the lane plumbing compiles away.
fn batch_invert_lanes<const K: usize>(values: &mut [Fp], scratch: &mut [Fp]) {
    let mut acc = [Fp::ONE; K];
    for (i, (value, slot)) in values.iter().zip(scratch.iter_mut()).enumerate() {
        *slot = acc[i % K];
        acc[i % K] *= *value;
    }
    // Join the K group products, invert once.
    let mut product = acc[0];
    for lane in &acc[1..] {
        product *= *lane;
    }
    let inverse = product.invert().unwrap();
    // Recover each group's inverse seed: g[j] = inverse * prod_{l != j} acc[l].
    let mut seeds = [inverse; K];
    if K > 1 {
        for (j, seed) in seeds.iter_mut().enumerate() {
            for (l, lane) in acc.iter().enumerate() {
                if l != j {
                    *seed *= *lane;
                }
            }
        }
    }
    // K independent back-substitution chains, interleaved.
    for i in (0..values.len()).rev() {
        let lane = i % K;
        let inverted = seeds[lane] * scratch[i];
        seeds[lane] *= values[i];
        values[i] = inverted;
    }
}

fn assert_correct<const K: usize>() {
    let mut rng = XorShiftRng::from_seed([0x1a; 16]);
    let original: Vec<Fp> = (0..37).map(|_| Fp::random(&mut rng)).collect();
    let mut values = original.clone();
    let mut scratch = vec![Fp::ZERO; values.len()];
    batch_invert_lanes::<K>(&mut values, &mut scratch);
    for (v, inv) in original.iter().zip(&values) {
        assert_eq!(*v * inv, Fp::ONE, "lane count {} incorrect", K);
    }
}

fn bench_batch_invert(c: &mut Criterion) {
    assert_correct::<1>();
    assert_correct::<2>();
    assert_correct::<3>();

    let mut rng = XorShiftRng::from_seed([0x2b; 16]);
    let mut group = c.benchmark_group("batch_invert");
    for &n in &[8usize, 16, 32, 64, 128, 256, 512, 1024, 4096, 16384, 65536] {
        let values: Vec<Fp> = (0..n).map(|_| Fp::random(&mut rng)).collect();
        group.throughput(Throughput::Elements(n as u64));
        for lanes in [1u32, 2, 3] {
            group.bench_with_input(
                BenchmarkId::new(format!("lanes{}", lanes), n),
                &values,
                |b, values| {
                    let mut scratch = vec![Fp::ZERO; values.len()];
                    b.iter_batched(
                        || values.clone(),
                        |mut values| {
                            match lanes {
                                1 => batch_invert_lanes::<1>(&mut values, &mut scratch),
                                2 => batch_invert_lanes::<2>(&mut values, &mut scratch),
                                _ => batch_invert_lanes::<3>(&mut values, &mut scratch),
                            }
                            values
                        },
                        BatchSize::LargeInput,
                    );
                },
            );
        }
    }
    group.finish();
}

criterion_group!(benches, bench_batch_invert);
criterion_main!(benches);
