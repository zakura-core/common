//! Pedersen and Merkle hashing microbenchmarks.
//!
//! Default features use the original 8-bit exp-window tables. Compare with:
//! `cargo bench -p zakura-sapling-crypto --bench pedersen_hash --features fused-pedersen`

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::{Rng, SeedableRng};
use rand_xorshift::XorShiftRng;
use sapling_crypto::{
    merkle_hash,
    pedersen_hash::{pedersen_hash, Personalization},
};

#[cfg(unix)]
use pprof::criterion::{Output, PProfProfiler};

const INPUT_CORPUS_SIZE: usize = 1 << 10;
const MERKLE_INPUT_BITS: usize = 510;
const NOTE_COMMITMENT_INPUT_BITS: usize = 64 + 256 + 256;
const RNG_SEED: [u8; 16] = *b"pedersen-bench-1";

fn random_bits(rng: &mut impl Rng, len: usize) -> Vec<bool> {
    (0..len)
        .map(|_| !rng.next_u32().is_multiple_of(2))
        .collect()
}

fn bench_pedersen_hash(c: &mut Criterion) {
    let rng = &mut XorShiftRng::from_seed(RNG_SEED);
    let cases = [
        ("merkle", Personalization::MerkleTree(31), MERKLE_INPUT_BITS),
        (
            "note-commitment",
            Personalization::NoteCommitment,
            NOTE_COMMITMENT_INPUT_BITS,
        ),
    ];

    let mut group = c.benchmark_group("pedersen-hash");
    for (name, personalization, input_bits) in cases {
        let corpus = (0..INPUT_CORPUS_SIZE)
            .map(|_| random_bits(rng, input_bits))
            .collect::<Vec<_>>();
        let mut index = 0;

        group.throughput(Throughput::Elements(input_bits as u64));
        group.bench_with_input(BenchmarkId::new(name, input_bits), &corpus, |b, corpus| {
            b.iter(|| {
                let bits = &corpus[index % corpus.len()];
                index += 1;
                pedersen_hash(personalization, bits.iter().copied())
            })
        });
    }
    group.finish();
}

/// Exercises the public Merkle hashing path with changing child nodes.
fn bench_merkle_hash(c: &mut Criterion) {
    let rng = &mut XorShiftRng::from_seed(RNG_SEED);
    let corpus = (0..INPUT_CORPUS_SIZE)
        .map(|_| {
            let mut lhs = [0u8; 32];
            let mut rhs = [0u8; 32];
            rng.fill_bytes(&mut lhs);
            rng.fill_bytes(&mut rhs);

            // Ensure each child is a valid little-endian field element.
            lhs[31] &= 0x3f;
            rhs[31] &= 0x3f;
            (lhs, rhs)
        })
        .collect::<Vec<_>>();
    let mut index = 0;

    c.bench_function("merkle-hash", |b| {
        b.iter(|| {
            let (lhs, rhs) = &corpus[index % corpus.len()];
            index += 1;
            merkle_hash(31, lhs, rhs)
        })
    });
}

#[cfg(unix)]
criterion_group! {
    name = benches;
    config = Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = bench_pedersen_hash, bench_merkle_hash
}
#[cfg(not(unix))]
criterion_group!(benches, bench_pedersen_hash, bench_merkle_hash);
criterion_main!(benches);
