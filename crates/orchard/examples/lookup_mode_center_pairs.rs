use std::{env, fs::OpenOptions, hint::black_box, io::Write, path::PathBuf, time::Instant};

use orchard::{
    Proof,
    circuit::{OrchardCircuitVersion, ProvingKey, VerifyingKey},
};
use rand::{SeedableRng, rngs::StdRng};

#[path = "../benches/support/mod.rs"]
mod support;

use support::{payment_fixture, two_real_spends_payment_fixture};

const ACTION_COUNTS: [usize; 3] = [1, 2, 4];
const WARMUP_PAIRS: u64 = 4;
const WARMUP_PROOF_SEED_DOMAIN: u8 = 0x24;
const MEASUREMENT_PROOF_SEED_DOMAIN: u8 = 0x25;

struct Measurement {
    pair: u64,
    proof_index: u64,
    action_position: usize,
    action_count: usize,
    control_first: bool,
    control_ns: u128,
    candidate_ns: u128,
    proof_len: usize,
}

fn proof_rng(domain: u8, action_count: usize, proof_index: u64) -> StdRng {
    let mut seed = [domain; 32];
    let action_count = u64::try_from(action_count).expect("Action count fits into u64");
    seed[..8].copy_from_slice(&action_count.to_le_bytes());
    seed[8..16].copy_from_slice(&proof_index.to_le_bytes());
    StdRng::from_seed(seed)
}

fn proof_index(block: u64, pairs_per_block: u64, pair: u64) -> u64 {
    block
        .checked_mul(pairs_per_block)
        .and_then(|offset| offset.checked_add(pair))
        .expect("proof index fits into u64")
}

fn select_control(control: bool) {
    // SAFETY: This diagnostic is the only environment mutator. It changes the
    // route only after the preceding proof, including all of its scoped Rayon
    // work, has completed and before the next proof begins.
    unsafe {
        if control {
            env::set_var("ZAKURA_LOOKUP_MODE_CENTER_CONTROL", "1");
        } else {
            env::remove_var("ZAKURA_LOOKUP_MODE_CENTER_CONTROL");
        }
    }
}

fn main() {
    let mut args = env::args_os().skip(1);
    let block = args
        .next()
        .expect("block index")
        .to_string_lossy()
        .parse::<u64>()
        .expect("numeric block index");
    let pair_count = args
        .next()
        .expect("pairs per Action count")
        .to_string_lossy()
        .parse::<u64>()
        .expect("numeric pair count");
    let output_path = PathBuf::from(args.next().expect("output path"));
    assert!(args.next().is_none());
    assert_ne!(pair_count, 0, "measure at least one pair");
    assert_eq!(pair_count % 2, 0, "use an even pair count to balance order");
    assert!(
        !output_path.exists(),
        "refusing to overwrite the output file"
    );
    assert!(
        env::var_os("ZAKURA_LOOKUP_REUSE_CONTROL").is_none(),
        "leave the merged lookup-reuse optimization enabled"
    );

    let expected_threads = env::var("IRONWOOD_K11_PROVER_THREADS")
        .expect("set IRONWOOD_K11_PROVER_THREADS")
        .parse::<usize>()
        .expect("numeric thread count");
    assert_eq!(rayon::current_num_threads(), expected_threads);

    let version = OrchardCircuitVersion::PostNu6_3;
    let verifying_key = VerifyingKey::build(version);
    let proving_key = ProvingKey::build(version);
    assert!(proving_key.prepare_proving());

    let fixtures = [
        payment_fixture(1),
        two_real_spends_payment_fixture(),
        payment_fixture(4),
    ];
    for (fixture, action_count) in fixtures.iter().zip(ACTION_COUNTS) {
        assert_eq!(fixture.bundle().actions().len(), action_count);
    }

    let action_count_len = u64::try_from(ACTION_COUNTS.len()).expect("Action count fits into u64");
    let rotation = usize::try_from(block % action_count_len)
        .expect("the Action-order rotation fits into usize");
    let action_order = [
        rotation,
        (rotation + 1) % ACTION_COUNTS.len(),
        (rotation + 2) % ACTION_COUNTS.len(),
    ];

    // Warm every circuit-count plan and both routes before any measurement.
    for &fixture_index in &action_order {
        let fixture = &fixtures[fixture_index];
        let action_count = ACTION_COUNTS[fixture_index];
        let authorization = fixture.bundle().authorization();
        for pair in 0..WARMUP_PAIRS {
            let warmup_index = proof_index(block, WARMUP_PAIRS, pair);
            let mut proofs = Vec::<Proof>::with_capacity(2);
            for control in [true, false] {
                select_control(control);
                proofs.push(
                    authorization
                        .create_proof(
                            &proving_key,
                            fixture.instances(),
                            proof_rng(WARMUP_PROOF_SEED_DOMAIN, action_count, warmup_index),
                        )
                        .unwrap(),
                );
            }
            assert_eq!(proofs[0].as_ref(), proofs[1].as_ref());
            proofs[0]
                .verify(&verifying_key, fixture.instances())
                .unwrap();
            black_box(proofs);
        }
    }

    let measurement_capacity = usize::try_from(pair_count)
        .expect("pair count fits into usize")
        .checked_mul(ACTION_COUNTS.len())
        .expect("measurement count fits into usize");
    let mut measurements = Vec::with_capacity(measurement_capacity);
    for pair in 0..pair_count {
        let current_proof_index = proof_index(block, pair_count, pair);
        let control_first = block % 2 == pair % 2;
        let route_order = if control_first {
            [true, false]
        } else {
            [false, true]
        };

        for (action_position, &fixture_index) in action_order.iter().enumerate() {
            let fixture = &fixtures[fixture_index];
            let action_count = ACTION_COUNTS[fixture_index];
            let authorization = fixture.bundle().authorization();
            let instances = fixture.instances();
            let mut control_ns = 0;
            let mut candidate_ns = 0;
            let mut proofs = Vec::<Proof>::with_capacity(2);

            for control in route_order {
                select_control(control);
                let rng = proof_rng(
                    MEASUREMENT_PROOF_SEED_DOMAIN,
                    action_count,
                    current_proof_index,
                );
                let started = Instant::now();
                let proof = authorization.create_proof(&proving_key, instances, rng);
                let elapsed_ns = started.elapsed().as_nanos();
                let proof = proof.unwrap();
                if control {
                    control_ns = elapsed_ns;
                } else {
                    candidate_ns = elapsed_ns;
                }
                proofs.push(proof);
            }

            assert_eq!(proofs[0].as_ref(), proofs[1].as_ref());
            let proof_len = proofs[0].as_ref().len();
            black_box(&proofs);
            measurements.push(Measurement {
                pair,
                proof_index: current_proof_index,
                action_position,
                action_count,
                control_first,
                control_ns,
                candidate_ns,
                proof_len,
            });
        }
    }

    // Format and write only after all timed proofs have completed.
    let mut output = Vec::new();
    writeln!(
        output,
        "block\tpair\tproof_index\taction_position\tactions\tfirst\tcontrol_ns\tcandidate_ns\tdelta_ns\tproof_len\tequal"
    )
    .unwrap();
    for measurement in measurements {
        let control_ns = i128::try_from(measurement.control_ns).expect("duration fits into i128");
        let candidate_ns =
            i128::try_from(measurement.candidate_ns).expect("duration fits into i128");
        writeln!(
            output,
            "{block}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\ttrue",
            measurement.pair,
            measurement.proof_index,
            measurement.action_position,
            measurement.action_count,
            if measurement.control_first {
                "control"
            } else {
                "candidate"
            },
            measurement.control_ns,
            measurement.candidate_ns,
            candidate_ns - control_ns,
            measurement.proof_len,
        )
        .unwrap();
    }

    let mut output_file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(output_path)
        .unwrap();
    output_file.write_all(&output).unwrap();
}
