use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use sapling_crypto::value::{CommitmentSum, NoteValue, ValueCommitTrapdoor, ValueCommitment};
use std::hint::black_box;

/// A fixed commitment value keeps fixture construction outside the timer.
const NOTE_VALUE: u64 = 100_000;
/// A canonical nonzero scalar with several nonzero limbs.
const TRAPDOOR_BYTES: [u8; 32] = [7; 32];
/// Zero, short signed balances, and the supported integer boundaries.
const BALANCES: [(&str, i64); 7] = [
    ("zero", 0),
    ("positive_fee", 50_000),
    ("negative_fee", -50_000),
    ("positive_coin", 100_000_000),
    ("negative_coin", -100_000_000),
    ("i64_max", i64::MAX),
    ("i64_min", i64::MIN),
];

fn binding_key(c: &mut Criterion) {
    let commitment = ValueCommitment::derive(
        NoteValue::from_raw(NOTE_VALUE),
        ValueCommitTrapdoor::from_bytes(TRAPDOOR_BYTES).unwrap(),
    );
    let sum = CommitmentSum::try_sum([&commitment]).unwrap();
    let mut group = c.benchmark_group("binding_key");
    for (name, balance) in BALANCES {
        group.bench_with_input(BenchmarkId::from_parameter(name), &balance, |b, balance| {
            b.iter(|| black_box(sum).into_bvk(black_box(*balance)))
        });
    }
    group.finish();
}

criterion_group!(benches, binding_key);
criterion_main!(benches);
