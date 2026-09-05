use std::{env, fs::OpenOptions, io::Write, path::PathBuf};

use orchard::{
    Anchor, Bundle,
    builder::{Builder, BundleType},
    bundle::{BundleVersion, Flags},
    circuit::{OrchardCircuitVersion, ProvingKey, VerifyingKey},
    keys::{FullViewingKey, Scope, SpendingKey},
    value::NoteValue,
};
use rand::{SeedableRng, rngs::StdRng};

const FIXTURE_ADDRESS_INDEX: u32 = 0;
const FIXTURE_NOTE_VALUE: u64 = 10;
const FIXTURE_MEMO_SIZE: usize = 512;
const FIXTURE_MEMO: [u8; FIXTURE_MEMO_SIZE] = [0; FIXTURE_MEMO_SIZE];
const FIXTURE_SPENDING_KEY: [u8; 32] = [7; 32];
const FIXTURE_ANCHOR: [u8; 32] = [0; 32];
const FIXTURE_SEED: [u8; 32] = [0x42; 32];
const PROOF_SEED: [u8; 32] = [0x24; 32];

fn main() {
    let mut args = env::args_os().skip(1);
    let action_count = args
        .next()
        .expect("action count")
        .to_string_lossy()
        .parse::<usize>()
        .expect("numeric action count");
    assert!(matches!(action_count, 1 | 2 | 4));
    let output = PathBuf::from(args.next().expect("output path"));
    assert!(args.next().is_none());

    let expected_threads = env::var("ORCHARD_K11_PROVER_THREADS")
        .expect("set ORCHARD_K11_PROVER_THREADS")
        .parse::<usize>()
        .expect("numeric thread count");
    assert_eq!(rayon::current_num_threads(), expected_threads);

    let version = OrchardCircuitVersion::PostNu6_3;
    let vk = VerifyingKey::build(version);
    let pk = ProvingKey::build(version);
    assert!(pk.prepare_proving(), "Pasta commitment tables must prepare");

    let sk = SpendingKey::from_bytes(FIXTURE_SPENDING_KEY).unwrap();
    let recipient = FullViewingKey::from(&sk).address_at(FIXTURE_ADDRESS_INDEX, Scope::External);
    let mut fixture_rng = StdRng::from_seed(FIXTURE_SEED);
    let mut builder = Builder::new(
        BundleType::Coinbase,
        BundleVersion::ironwood_v3(),
        Flags::SPENDS_DISABLED,
        Anchor::from_bytes(FIXTURE_ANCHOR).unwrap(),
    )
    .unwrap();
    for _ in 0..action_count {
        builder
            .add_output(
                None,
                recipient,
                NoteValue::from_raw(FIXTURE_NOTE_VALUE),
                FIXTURE_MEMO,
            )
            .unwrap();
    }
    let bundle: Bundle<_, i64> = builder
        .build(&mut fixture_rng)
        .unwrap()
        .expect("at least one output produces a bundle")
        .0;
    assert_eq!(bundle.actions().len(), action_count);
    let instances = bundle
        .actions()
        .iter()
        .map(|action| action.to_instance(*bundle.flags(), *bundle.anchor()))
        .collect::<Vec<_>>();
    if let Ok(seconds) = env::var("ZAKURA_PROFILE_READY_SLEEP_SECONDS") {
        std::thread::sleep(std::time::Duration::from_secs(
            seconds.parse().expect("numeric ready sleep"),
        ));
    }
    let repeats = env::var("ZAKURA_SAMPLE_REPEATS")
        .map(|value| value.parse::<usize>().expect("numeric repeat count"))
        .unwrap_or(1);
    let mut proof = None;
    for repeat in 0..repeats {
        let mut seed = PROOF_SEED;
        seed[..8].copy_from_slice(&(repeat as u64).to_le_bytes());
        proof = Some(
            bundle
                .authorization()
                .create_proof(&pk, &instances, StdRng::from_seed(seed))
                .unwrap(),
        );
    }
    let proof = proof.expect("positive repeat count");
    proof.verify(&vk, &instances).unwrap();

    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(output)
        .unwrap();
    output.write_all(proof.as_ref()).unwrap();
    println!(
        "actions={action_count} proof_bytes={}",
        proof.as_ref().len()
    );
}
