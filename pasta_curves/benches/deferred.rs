///! Benchmarks for deferred (lazy-reduction) inner products.
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

use pasta_curves::deferred::DeferredField;
use pasta_curves::{Fp, Fq};

const SIZES: [usize; 3] = [100, 1024, 10000];

fn bench_field<F: DeferredField>(c: &mut Criterion, name: &str) {
    let mut group = c.benchmark_group(name);

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    for n in SIZES {
        let a: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
        let b: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();

        // The deferred accumulator: one reduction for the whole inner product.
        group.bench_function(BenchmarkId::new("inner_product_lazy", n), |bench| {
            bench.iter(|| {
                let mut acc = F::Accumulator::default();
                for (x, y) in a.iter().zip(b.iter()) {
                    F::mul_accumulate(&mut acc, x, y);
                }
                F::reduce(acc)
            })
        });

        // The eager floor: reduce every product, accumulate with field adds.
        group.bench_function(BenchmarkId::new("inner_product_eager", n), |bench| {
            bench.iter(|| {
                let mut acc = F::ZERO;
                for (x, y) in a.iter().zip(b.iter()) {
                    acc += *x * *y;
                }
                acc
            })
        });
    }

    group.finish();
}

fn criterion_benchmark(c: &mut Criterion) {
    bench_field::<Fp>(c, "Fp-deferred");
    bench_field::<Fq>(c, "Fq-deferred");
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
