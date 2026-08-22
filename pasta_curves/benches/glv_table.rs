//! Microbenchmarks for building and consuming GLV tables.

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use ff::Field;
use pasta_curves::glv::{Decomposed, GlvParams, Table};
use pasta_curves::{pallas, vesta};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

// A large batch amortizes the one shared inversion and makes the table
// materialization work visible without growing the output beyond 256 KiB.
const TABLE_BUILD_BATCH_SIZE: usize = 256;

// One table use is short enough for surrounding benchmark noise to matter.
// A corpus also exercises the table across many full-width digit schedules.
const TABLE_USE_CORPUS_SIZE: usize = 16;
const RNG_SEED: [u8; 16] = [0x42; 16];

fn criterion_benchmark(c: &mut Criterion) {
    table_bench::<pallas::Point>(c, "Pallas");
    table_bench::<vesta::Point>(c, "Vesta");
}

fn table_bench<C: GlvParams>(c: &mut Criterion, curve_name: &str) {
    let mut rng = XorShiftRng::from_seed(RNG_SEED);
    let points: Vec<C> = (0..TABLE_BUILD_BATCH_SIZE)
        .map(|_| C::generator() * C::ScalarExt::random(&mut rng))
        .collect();

    let scalars: Vec<C::ScalarExt> = (0..TABLE_USE_CORPUS_SIZE)
        .map(|_| C::ScalarExt::random(&mut rng))
        .collect();
    let decomposed: Vec<Decomposed<C>> = scalars.iter().map(Decomposed::new).collect();
    let table = Table::new(&points[0]);

    // Keep the consumer honest before measuring it. The crate's unit tests
    // cover the individual digit mappings in more detail.
    for (scalar, decomposed) in scalars.iter().zip(&decomposed) {
        assert!(table.mul_decomposed(decomposed) == points[0] * scalar);
    }

    let mut group = c.benchmark_group(format!("{curve_name}/GLV table micro"));

    group.throughput(Throughput::Elements(TABLE_BUILD_BATCH_SIZE as u64));
    group.bench_function(format!("build batch of {TABLE_BUILD_BATCH_SIZE}"), |b| {
        b.iter(|| black_box(Table::batch(black_box(points.as_slice()))))
    });

    group.throughput(Throughput::Elements(TABLE_USE_CORPUS_SIZE as u64));
    group.bench_function(
        format!("use prebuilt table with {TABLE_USE_CORPUS_SIZE} scalars"),
        |b| {
            b.iter(|| {
                let table = black_box(&table);
                for scalar in black_box(decomposed.as_slice()) {
                    black_box(table.mul_decomposed(scalar));
                }
            })
        },
    );

    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
