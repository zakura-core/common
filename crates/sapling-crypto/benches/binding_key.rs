use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use sapling_crypto::value::{
    CommitmentSum, NoteValue, TrapdoorSum, ValueCommitTrapdoor, ValueCommitment,
};
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

fn binding_key_batch(c: &mut Criterion) {
    let mut rng = rand::rng();
    let msg = b"BindingKeyBatchBenchmark";
    let fixtures: Vec<_> = (0..32)
        .map(|i| {
            let mut bytes = TRAPDOOR_BYTES;
            bytes[0] += i;
            let trapdoor = ValueCommitTrapdoor::from_bytes(bytes).unwrap();
            let bsk = (TrapdoorSum::zero() + &trapdoor).into_bsk();
            let commitment = ValueCommitment::derive(NoteValue::ZERO, trapdoor);
            let sum = CommitmentSum::try_sum([&commitment]).unwrap();
            (sum, bsk.sign(&mut rng, msg))
        })
        .collect();
    let mut group = c.benchmark_group("binding_key_batch");
    for n in [1, 8, 32] {
        for retain_point in [false, true] {
            let path = if retain_point { "point" } else { "bytes" };
            group.bench_with_input(BenchmarkId::new(path, n), &n, |b, &n| {
                b.iter(|| {
                    let mut batch = redjubjub::batch::Verifier::new();
                    for (sum, sig) in &fixtures[..n] {
                        let bvk = black_box(*sum).into_bvk(black_box(0));
                        if retain_point {
                            batch.queue(redjubjub::batch::Item::from_binding_key(bvk, *sig, msg));
                        } else {
                            batch.queue((bvk.into(), *sig, msg));
                        }
                    }
                    batch.verify(&mut rng).unwrap();
                })
            });
        }
    }
    group.finish();
}

criterion_group!(benches, binding_key, binding_key_batch);
criterion_main!(benches);
