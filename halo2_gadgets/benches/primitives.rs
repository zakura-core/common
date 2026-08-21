use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use ff::Field;
use group::{Curve, Group};
use halo2_gadgets::{
    ecc::chip::constants::{
        compute_lagrange_coeffs, compute_pallas_lagrange_coeffs, NUM_WINDOWS, NUM_WINDOWS_SHORT,
    },
    poseidon::primitives::{self as poseidon, ConstantLength, P128Pow5T3},
    sinsemilla::primitives as sinsemilla,
};

use pasta_curves::pallas;
#[cfg(unix)]
use pprof::criterion::{Output, PProfProfiler};
use rand::{rng, RngExt};

fn bench_primitives(c: &mut Criterion) {
    let mut rng = rng();

    {
        let mut group = c.benchmark_group("Fixed-base table construction");
        let base = pallas::Point::generator().to_affine();

        for num_windows in [NUM_WINDOWS_SHORT, NUM_WINDOWS] {
            group.bench_function(BenchmarkId::new("generic", num_windows), |b| {
                b.iter(|| compute_lagrange_coeffs(black_box(base), num_windows))
            });
            group.bench_function(BenchmarkId::new("pallas", num_windows), |b| {
                b.iter(|| compute_pallas_lagrange_coeffs(black_box(base), num_windows))
            });
        }
    }

    {
        let mut group = c.benchmark_group("Poseidon");

        let message = [
            pallas::Base::random(&mut rng),
            pallas::Base::random(&mut rng),
        ];

        group.bench_function("2-to-1", |b| {
            b.iter(|| {
                poseidon::Hash::<_, P128Pow5T3, ConstantLength<2>, 3, 2>::init().hash(message)
            })
        });
    }

    {
        let mut group = c.benchmark_group("Sinsemilla");

        let hasher = sinsemilla::HashDomain::new("hasher");
        let committer = sinsemilla::CommitDomain::new("committer");
        let bits: Vec<bool> = (0..1086).map(|_| rng.random()).collect();
        let r = pallas::Scalar::random(&mut rng);

        // Benchmark the input sizes we use in Orchard:
        // - 510 bits for Commit^ivk
        // - 520 bits for MerkleCRH
        // - 1086 bits for NoteCommit
        for size in [510, 520, 1086] {
            group.bench_function(BenchmarkId::new("hash-to-point", size), |b| {
                b.iter(|| hasher.hash_to_point(bits[..size].iter().cloned()))
            });

            group.bench_function(BenchmarkId::new("hash", size), |b| {
                b.iter(|| hasher.hash(bits[..size].iter().cloned()))
            });

            group.bench_function(BenchmarkId::new("commit", size), |b| {
                b.iter(|| committer.commit(bits[..size].iter().cloned(), &r))
            });

            group.bench_function(BenchmarkId::new("short-commit", size), |b| {
                b.iter(|| committer.commit(bits[..size].iter().cloned(), &r))
            });
        }
    }
}

#[cfg(unix)]
criterion_group! {
    name = benches;
    config = Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = bench_primitives
}
#[cfg(not(unix))]
criterion_group!(benches, bench_primitives);
criterion_main!(benches);
