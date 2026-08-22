//! Pedersen and Merkle hashing microbenchmarks.
//!
//! Default features use the original 8-bit exp-window tables. Compare with:
//! `cargo bench -p zakura-sapling-crypto --bench pedersen_hash --features fused-pedersen`

use criterion::{criterion_group, criterion_main, Criterion};
use rand::Rng;
use sapling_crypto::{
    merkle_hash,
    pedersen_hash::{pedersen_hash, Personalization},
};

#[cfg(unix)]
use pprof::criterion::{Output, PProfProfiler};

fn bench_pedersen_hash(c: &mut Criterion) {
    let rng = &mut rand::rng();
    let bits = (0..510)
        .map(|_| !rng.next_u32().is_multiple_of(2))
        .collect::<Vec<_>>();
    let personalization = Personalization::MerkleTree(31);

    c.bench_function("pedersen-hash", |b| {
        b.iter(|| pedersen_hash(personalization, bits.clone()))
    });
}

/// Exercises the full Merkle tree hashing path (`Node::combine` -> `pedersen_hash`).
fn bench_merkle_hash(c: &mut Criterion) {
    let rng = &mut rand::rng();
    let mut leaf = || {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        // Clear the top bits so each child is a valid little-endian field element.
        bytes[31] &= 0x3f;
        bytes
    };
    let lhs = leaf();
    let rhs = leaf();

    c.bench_function("merkle-hash", |b| b.iter(|| merkle_hash(31, &lhs, &rhs)));
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
