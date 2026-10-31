use criterion::{Criterion, criterion_group, criterion_main};
use rand::Rng;
use sapling_crypto::{
    merkle_hash,
    pedersen_hash::{Personalization, pedersen_hash},
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

fn bench_merkle_hash(c: &mut Criterion) {
    let rng = &mut rand::rng();
    let mut lhs = [0u8; 32];
    let mut rhs = [0u8; 32];
    rng.fill_bytes(&mut lhs);
    rng.fill_bytes(&mut rhs);

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
