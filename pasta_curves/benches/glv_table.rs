//! Microbenchmarks for building and consuming GLV tables.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ff::Field;
use pasta_curves::glv::{bench_internals, Decomposed, GlvParams, Table};
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

// Forced same-build comparison grid for the effective-affine experiment:
// normalized (shared batch normalization) versus effective (inversion-free
// global-Z chain) construction, and construction-plus-consumption so a
// builder win cannot be reported without its downstream cost.
const FORCED_BUILD_SIZES: [usize; 11] = [1, 8, 16, 32, 50, 64, 128, 256, 512, 2048, 4096];
// Build-plus-use only at sizes where both backends run the batch-affine
// ladder kernel, so the rows differ in table representation alone.
const FORCED_BUILD_MUL_SIZES: [usize; 5] = [32, 64, 256, 1024, 4096];

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

    forced_backend_bench::<C>(c, curve_name);
}

/// The forced normalized/effective comparison rows.
fn forced_backend_bench<C: GlvParams>(c: &mut Criterion, curve_name: &str) {
    let mut rng = XorShiftRng::from_seed(RNG_SEED);
    let max = *FORCED_BUILD_SIZES.iter().max().unwrap();
    let points: Vec<C> = (0..max)
        .map(|_| C::generator() * C::ScalarExt::random(&mut rng))
        .collect();
    let scalar = C::ScalarExt::random(&mut rng);
    let decomposed = Decomposed::<C>::new(&scalar);

    // Keep both consumers honest before measuring them.
    {
        let tables = Table::batch(&points[..4]);
        let refs: Vec<&Table<C>> = tables.iter().collect();
        let normalized = Table::mul_decomposed_batch(&refs, &decomposed);
        let effective = bench_internals::effective_mul_decomposed_batch(
            &bench_internals::effective_table_batch(&points[..4]),
            &decomposed,
        );
        for ((point, normalized), effective) in points.iter().zip(normalized).zip(effective) {
            assert!(normalized == *point * scalar);
            assert!(effective == *point * scalar);
        }
    }

    let mut group = c.benchmark_group(format!("{curve_name}/forced table build"));
    for size in FORCED_BUILD_SIZES {
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(BenchmarkId::new("normalized", size), &size, |b, _| {
            b.iter(|| black_box(Table::batch(black_box(&points[..size]))))
        });
        group.bench_with_input(BenchmarkId::new("effective", size), &size, |b, _| {
            b.iter(|| {
                black_box(bench_internals::effective_table_batch(black_box(
                    &points[..size],
                )))
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group(format!("{curve_name}/forced table build+mul"));
    group.sample_size(20);
    for size in FORCED_BUILD_MUL_SIZES {
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(BenchmarkId::new("normalized", size), &size, |b, _| {
            b.iter(|| {
                let tables = Table::batch(black_box(&points[..size]));
                let refs: Vec<&Table<C>> = tables.iter().collect();
                black_box(Table::mul_decomposed_batch(&refs, black_box(&decomposed)))
            })
        });
        group.bench_with_input(BenchmarkId::new("effective", size), &size, |b, _| {
            b.iter(|| {
                let tables = bench_internals::effective_table_batch(black_box(&points[..size]));
                black_box(bench_internals::effective_mul_decomposed_batch(
                    &tables,
                    black_box(&decomposed),
                ))
            })
        });
    }
    group.finish();

    // Reused prebuilt tables: the ladder must not care which
    // representation feeds it (the reuse gate).
    let mut group = c.benchmark_group(format!("{curve_name}/forced table reuse"));
    group.sample_size(20);
    let reuse_size = TABLE_BUILD_BATCH_SIZE;
    let corpus: Vec<Decomposed<C>> = (0..TABLE_USE_CORPUS_SIZE)
        .map(|_| Decomposed::new(&C::ScalarExt::random(&mut rng)))
        .collect();
    let normalized_tables = Table::batch(&points[..reuse_size]);
    let normalized_refs: Vec<&Table<C>> = normalized_tables.iter().collect();
    let effective_tables = bench_internals::effective_table_batch(&points[..reuse_size]);
    group.throughput(Throughput::Elements((reuse_size * corpus.len()) as u64));
    group.bench_function(
        format!("normalized/{reuse_size}x{TABLE_USE_CORPUS_SIZE}"),
        |b| {
            b.iter(|| {
                for scalar in black_box(corpus.as_slice()) {
                    black_box(Table::mul_decomposed_batch(
                        black_box(&normalized_refs),
                        scalar,
                    ));
                }
            })
        },
    );
    group.bench_function(
        format!("effective/{reuse_size}x{TABLE_USE_CORPUS_SIZE}"),
        |b| {
            b.iter(|| {
                for scalar in black_box(corpus.as_slice()) {
                    black_box(bench_internals::effective_mul_decomposed_batch(
                        black_box(&effective_tables),
                        scalar,
                    ));
                }
            })
        },
    );
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
