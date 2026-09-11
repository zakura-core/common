use std::{env, time::Instant};

use orchard::circuit::{OrchardCircuitVersion, ProvingKey, VerifyingKey};
use rand::{SeedableRng, rngs::StdRng};

#[path = "../benches/support/mod.rs"]
mod support;

const PROOF_SEED_DOMAIN: u8 = 0x26;

fn main() {
    let mut args = env::args().skip(1);
    let action_count = args
        .next()
        .expect("action count")
        .parse::<usize>()
        .expect("numeric action count");
    let sample_index = args
        .next()
        .expect("sample index")
        .parse::<u64>()
        .expect("numeric sample index");
    assert!(args.next().is_none());

    let fixture = support::payment_fixture_with_index(action_count, sample_index);
    let version = OrchardCircuitVersion::PostNu6_3;
    let vk = VerifyingKey::build(version);
    let pk = ProvingKey::build(version);
    assert!(pk.prepare_proving());

    let mut seed = [PROOF_SEED_DOMAIN; 32];
    seed[..8].copy_from_slice(
        &u64::try_from(action_count)
            .expect("Action count fits into u64")
            .to_le_bytes(),
    );
    seed[8..16].copy_from_slice(&sample_index.to_le_bytes());

    let start = Instant::now();
    let proof = fixture
        .bundle()
        .authorization()
        .create_proof(&pk, fixture.instances(), StdRng::from_seed(seed))
        .expect("proof creation succeeds");
    let elapsed = start.elapsed();
    proof
        .verify(&vk, fixture.instances())
        .expect("proof verification succeeds");

    let hash = blake2b_simd::Params::new()
        .hash_length(32)
        .hash(proof.as_ref());
    println!(
        "sample={sample_index} actions={action_count} ns={} bytes={} hash={}",
        elapsed.as_nanos(),
        proof.as_ref().len(),
        hash.to_hex(),
    );
}
