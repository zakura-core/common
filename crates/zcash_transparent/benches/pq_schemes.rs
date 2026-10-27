//! Compares the post-quantum account signature schemes on key generation, signing and
//! verification, each measured through the same interface the account rules use.

use core::hint::black_box;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use zcash_transparent::pq::{
    KeySeed, master_from_seed,
    scheme::{SignatureScheme, SlhDsa, WotsPlus},
};

const DIGEST: [u8; 32] = [7; 32];

fn seed() -> KeySeed {
    KeySeed::new(&master_from_seed(&[1; 32]), 0, 0, 0)
}

fn bench_scheme<S: SignatureScheme>(c: &mut Criterion, name: &str) {
    let mut group = c.benchmark_group("pq_scheme");

    // Key generation: deriving a spare's secret key and computing the public key it commits to.
    group.bench_function(BenchmarkId::new("keygen", name), |b| {
        b.iter(|| {
            let key = S::derive(black_box(&seed())).unwrap();
            S::public_key(&key)
        })
    });

    group.bench_function(BenchmarkId::new("sign", name), |b| {
        b.iter_batched(
            || S::derive(&seed()).unwrap(),
            |key| S::sign(key, black_box(&DIGEST)),
            criterion::BatchSize::SmallInput,
        )
    });

    // Verification: checking a witness and recovering the public key the account commits to.
    let witness = S::sign(S::derive(&seed()).unwrap(), &DIGEST);
    group.bench_function(BenchmarkId::new("verify", name), |b| {
        b.iter(|| S::recover(black_box(&DIGEST), black_box(&witness)).unwrap())
    });

    group.finish();
}

fn pq_schemes(c: &mut Criterion) {
    bench_scheme::<WotsPlus>(c, "WOTS+ n32 w16");
    bench_scheme::<SlhDsa<slh_dsa::Sha2_128s>>(c, "SLH-DSA-SHA2-128s");
    bench_scheme::<SlhDsa<slh_dsa::Sha2_128f>>(c, "SLH-DSA-SHA2-128f");
    bench_scheme::<SlhDsa<slh_dsa::Sha2_256s>>(c, "SLH-DSA-SHA2-256s");
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = pq_schemes
}
criterion_main!(benches);
