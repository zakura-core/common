use criterion::{Criterion, criterion_group, criterion_main};
use orchard::{
    keys::{FullViewingKey, Scope, SpendingKey},
    note::{Note, NoteVersion, RandomSeed, Rho},
    value::{NoteValue, ValueCommitTrapdoor, ValueCommitment},
};
use std::hint::black_box;

/// A nonzero canonical scalar encoding with several nonzero limbs.
const TRAPDOOR_BYTES: [u8; 32] = [7; 32];
/// Fixed valid key material keeps setup out of the measured operations.
const SPENDING_KEY_BYTES: [u8; 32] = [8; 32];
/// A deterministic note seed used only for benchmark fixtures.
const NOTE_SEED: [u8; 32] = [9; 32];
/// A fee-sized amount exercises short value scalars and a full-width trapdoor.
const VALUE_MAGNITUDE: u64 = 50_000;

fn legacy_scalar_mul(c: &mut Criterion) {
    let value = NoteValue::from_raw(VALUE_MAGNITUDE) - NoteValue::ZERO;
    let trapdoor = ValueCommitTrapdoor::from_bytes(TRAPDOOR_BYTES).unwrap();
    let sk = SpendingKey::from_bytes(SPENDING_KEY_BYTES).unwrap();
    let fvk = FullViewingKey::from(&sk);
    let recipient = fvk.address_at(0u32, Scope::External);
    let rho = Rho::from_bytes(&[0; 32]).unwrap();
    let seed = RandomSeed::from_bytes(NOTE_SEED, &rho).unwrap();
    let note = Note::from_parts(
        recipient,
        NoteValue::from_raw(VALUE_MAGNITUDE),
        rho,
        seed,
        NoteVersion::V2,
    )
    .unwrap();

    // Warm the lazy tables before collecting steady-state measurements.
    black_box(ValueCommitment::derive(value, trapdoor.clone()));
    black_box(note.nullifier(&fvk));

    let mut group = c.benchmark_group("legacy_scalar_mul");
    group.bench_function("value_commitment", |b| {
        b.iter(|| ValueCommitment::derive(black_box(value), black_box(trapdoor.clone())))
    });
    group.bench_function("nullifier", |b| {
        b.iter(|| black_box(&note).nullifier(black_box(&fvk)))
    });
    group.finish();
}

criterion_group!(benches, legacy_scalar_mul);
criterion_main!(benches);
