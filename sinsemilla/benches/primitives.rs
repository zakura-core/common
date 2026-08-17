use std::{collections::BTreeSet, hint::black_box};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use pasta_curves::pallas;
use sinsemilla::{CommitDomain, HashDomain, K};

const ORCHARD_NOTE_COMMITMENT_BITS: usize = 1_086;
const NOTE_COMMITMENT_DOMAIN: &str = "z.cash:Orchard-NoteCommit";
const BENCHMARK_TRAPDOOR: u64 = 42;
const FIXTURE_SEED: u64 = 0x4f72_6368_6172_6421;

fn message_bits() -> Vec<bool> {
    let mut state = FIXTURE_SEED;
    (0..ORCHARD_NOTE_COMMITMENT_BITS)
        .map(|_| {
            // SplitMix64 gives the deterministic fixture a representative
            // spread across the 1,024-entry generator table.
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut mixed = state;
            mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            ((mixed ^ (mixed >> 31)) >> 63) != 0
        })
        .collect()
}

fn distinct_words(bits: &[bool]) -> usize {
    bits.chunks_exact(K)
        .map(|word| {
            word.iter()
                .enumerate()
                .fold(0_u16, |value, (bit, set)| value | (u16::from(*set) << bit))
        })
        .collect::<BTreeSet<_>>()
        .len()
}

fn benchmark_primitives(c: &mut Criterion) {
    let bits = message_bits();
    let hash_domain = HashDomain::new(NOTE_COMMITMENT_DOMAIN);
    let commit_domain = CommitDomain::new(NOTE_COMMITMENT_DOMAIN);
    let trapdoor = pallas::Scalar::from(BENCHMARK_TRAPDOOR);
    assert!(distinct_words(&bits) >= 100);
    assert!(bool::from(
        hash_domain.hash_to_point(bits.iter().copied()).is_some()
    ));
    assert!(bool::from(
        commit_domain
            .commit(bits.iter().copied(), &trapdoor)
            .is_some()
    ));
    let mut group = c.benchmark_group("sinsemilla");

    group.bench_with_input(
        BenchmarkId::new("hash-to-point", ORCHARD_NOTE_COMMITMENT_BITS),
        &bits,
        |bencher, bits| {
            bencher.iter(|| black_box(hash_domain.hash_to_point(bits.iter().copied())));
        },
    );
    group.bench_with_input(
        BenchmarkId::new("commit", ORCHARD_NOTE_COMMITMENT_BITS),
        &bits,
        |bencher, bits| {
            bencher.iter(|| black_box(commit_domain.commit(bits.iter().copied(), &trapdoor)));
        },
    );
}

criterion_group!(benches, benchmark_primitives);
criterion_main!(benches);
