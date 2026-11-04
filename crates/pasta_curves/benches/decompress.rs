//! Point decompression: one at a time versus `batch_from_bytes`.
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use group::{Group, GroupEncoding};
use pasta_curves::{pallas, vesta};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::hint::black_box;

macro_rules! bench_curve {
    ($c:expr, $name:literal, $affine:ty, $group:ty) => {{
        let mut rng = XorShiftRng::from_seed([3; 16]);
        let mut g = $c.benchmark_group(concat!("decompress/", $name));
        for n in [1usize, 2, 5, 8, 64] {
            let bytes: Vec<[u8; 32]> = (0..n)
                .map(|_| <$group>::random(&mut rng).to_bytes())
                .collect();
            g.throughput(Throughput::Elements(n as u64));
            g.bench_function(BenchmarkId::new("from_bytes", n), |b| {
                b.iter(|| {
                    black_box(&bytes)
                        .iter()
                        .map(<$affine>::from_bytes)
                        .collect::<Vec<_>>()
                })
            });
            g.bench_function(BenchmarkId::new("batch_from_bytes", n), |b| {
                b.iter(|| <$affine>::batch_from_bytes(black_box(&bytes).iter().copied()))
            });
        }
        g.finish();
    }};
}

fn bench(c: &mut Criterion) {
    bench_curve!(c, "pallas", pallas::Affine, pallas::Point);
    bench_curve!(c, "vesta", vesta::Affine, vesta::Point);
}

criterion_group!(benches, bench);
criterion_main!(benches);
