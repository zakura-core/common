use std::{env, time::Instant};

use orchard::{
    Anchor, Bundle,
    builder::{Builder, BundleType},
    bundle::{BundleVersion, Flags},
    circuit::{OrchardCircuitVersion, ProvingKey},
    keys::{FullViewingKey, Scope, SpendingKey},
    value::NoteValue,
};
use rand::{SeedableRng, rngs::StdRng};

const FIXTURE_MEMO: [u8; 512] = [0; 512];

fn main() {
    let mut args = env::args().skip(1);
    let label = args.next().expect("variant label");
    let action_count = args
        .next()
        .expect("action count")
        .parse::<usize>()
        .expect("action count is an integer");
    let sample = args
        .next()
        .expect("sample index")
        .parse::<u64>()
        .expect("sample index is an integer");
    assert!(args.next().is_none(), "unexpected arguments");
    assert!([1, 2, 4].contains(&action_count));

    let version = OrchardCircuitVersion::FixedPostNu6_2;
    let spending_key = SpendingKey::from_bytes([7; 32]).unwrap();
    let recipient = FullViewingKey::from(&spending_key).address_at(0usize, Scope::External);
    let mut fixture_seed = [0x42; 32];
    fixture_seed[..8].copy_from_slice(&(action_count as u64).to_le_bytes());
    let mut fixture_rng = StdRng::from_seed(fixture_seed);
    let mut builder = Builder::new(
        BundleType::Coinbase,
        BundleVersion::orchard_v2(),
        Flags::SPENDS_DISABLED,
        Anchor::from_bytes([0; 32]).unwrap(),
    )
    .unwrap();
    for _ in 0..action_count {
        builder
            .add_output(None, recipient, NoteValue::from_raw(10), FIXTURE_MEMO)
            .unwrap();
    }
    let bundle: Bundle<_, i64> = builder
        .build(&mut fixture_rng)
        .unwrap()
        .expect("at least one output creates a bundle")
        .0;
    assert_eq!(bundle.actions().len(), action_count);
    let instances = bundle
        .actions()
        .iter()
        .map(|action| action.to_instance(*bundle.flags(), *bundle.anchor()))
        .collect::<Vec<_>>();

    let started = Instant::now();
    let proving_key = ProvingKey::build(version);
    let keygen_ms = started.elapsed().as_secs_f64() * 1_000.0;

    let started = Instant::now();
    assert!(proving_key.prepare_proving());
    let prepare_ms = started.elapsed().as_secs_f64() * 1_000.0;

    let mut proof_seed = [0x26; 32];
    proof_seed[..8].copy_from_slice(&(action_count as u64).to_le_bytes());
    proof_seed[8..16].copy_from_slice(&sample.to_le_bytes());
    let started = Instant::now();
    let proof = bundle
        .authorization()
        .create_proof(&proving_key, &instances, StdRng::from_seed(proof_seed))
        .expect("proof creation succeeds");
    let proof_ms = started.elapsed().as_secs_f64() * 1_000.0;
    if let Some(path) = env::var_os("PROOF_OUT") {
        std::fs::write(path, proof.as_ref()).expect("proof output is writable");
    }

    let verifying_key = proving_key.verifying_key();
    let started = Instant::now();
    proof
        .verify(&verifying_key, &instances)
        .expect("proof verifies");
    let verify_ms = started.elapsed().as_secs_f64() * 1_000.0;

    println!(
        "{label}\t{action_count}\t{sample}\t{keygen_ms:.6}\t{prepare_ms:.6}\t{proof_ms:.6}\t{verify_ms:.6}\t{}",
        proof.as_ref().len(),
    );
}
