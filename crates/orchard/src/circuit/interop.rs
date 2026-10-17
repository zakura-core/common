//! Cross-process compatibility: each test binary links exactly one backend and only the
//! proof role it exercises, so a prover-only producer must agree with a verifier-only
//! consumer.
use super::*;
use std::{fs, path::PathBuf};

/// Small and non-power-of-two action counts exercise padding and shared transcripts.
const ACTION_COUNTS: [u8; 3] = [1, 2, 3];
/// Deterministic public test seed; never used for real transactions.
#[cfg(all(feature = "prover", feature = "zip32-addresses"))]
const FIXTURE_SEED: [u8; 32] = [0x53; 32];
/// Each fixture field uses its canonical protocol encoding.
#[cfg(feature = "verifier")]
const FIELD_BYTES: usize = 32;

fn directory() -> PathBuf {
    std::env::var_os("ORCHARD_INTEROP_DIR")
        .expect("set ORCHARD_INTEROP_DIR")
        .into()
}

#[cfg(all(feature = "prover", feature = "zip32-addresses"))]
fn write_instances(path: PathBuf, instances: &[Instance]) {
    use std::io::Write;

    let mut file = fs::File::create(path).unwrap();
    for instance in instances {
        for field in [
            instance.anchor.to_bytes(),
            instance.cv_net.to_bytes(),
            instance.nf_old.to_bytes(),
            instance.rk.clone().into(),
            instance.cmx.to_bytes(),
        ] {
            file.write_all(&field).unwrap();
        }
        let flags = u8::from(instance.enable_spend)
            | (u8::from(instance.enable_output) << 1)
            | (u8::from(!instance.cross_address_disabled) << 2);
        file.write_all(&[flags]).unwrap();
    }
}

#[cfg(feature = "verifier")]
fn read_instances(path: PathBuf, count: u8) -> alloc::vec::Vec<Instance> {
    use crate::bundle::BundleVersion;
    use std::io::Read;

    let mut file = fs::File::open(path).unwrap();
    fn field(file: &mut fs::File) -> [u8; FIELD_BYTES] {
        let mut bytes = [0; FIELD_BYTES];
        file.read_exact(&mut bytes).unwrap();
        bytes
    }
    // Each record is five canonical domain encodings followed by a canonical Ironwood flag byte.
    let mut result = alloc::vec::Vec::new();
    for _ in 0..count {
        let anchor = Anchor::from_bytes(field(&mut file)).unwrap();
        let cv = ValueCommitment::from_bytes(&field(&mut file)).unwrap();
        let nf = Nullifier::from_bytes(&field(&mut file)).unwrap();
        let rk = VerificationKey::try_from(field(&mut file)).unwrap();
        let cmx = ExtractedNoteCommitment::from_bytes(&field(&mut file)).unwrap();
        let mut flags = [0];
        file.read_exact(&mut flags).unwrap();
        result.push(
            Instance::from_parts(
                anchor,
                cv,
                nf,
                rk,
                cmx,
                Flags::from_byte(flags[0], BundleVersion::ironwood_v3()).unwrap(),
            )
            .unwrap(),
        );
    }
    let mut remaining = alloc::vec::Vec::new();
    file.read_to_end(&mut remaining).unwrap();
    assert!(remaining.is_empty());
    result
}

#[cfg(all(feature = "prover", feature = "zip32-addresses"))]
#[test]
#[ignore = "run by check_orchard_backends.py in separate backend builds"]
fn export_backend_proofs() {
    use crate::builder::testing::build_pinned_fixture_bundle;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    fs::create_dir_all(directory()).unwrap();
    let pk = crate::cached_test_keys(OrchardCircuitVersion::PostNu6_3).proving_key();
    for count in ACTION_COUNTS {
        for restricted in [false, true] {
            let mut rng = ChaCha20Rng::from_seed(FIXTURE_SEED);
            let bundle = build_pinned_fixture_bundle(&mut rng, count);
            let mut instances = bundle.to_instances();
            for instance in &mut instances {
                instance.cross_address_disabled = restricted;
            }
            let proof = bundle
                .authorization()
                .create_proof(pk, &instances, &mut rng)
                .unwrap();
            // The consumer build is the one that verifies; a producer that also links
            // the verifier checks its own output first.
            #[cfg(feature = "verifier")]
            {
                proof.verify(&pk.verifying_key(), &instances).unwrap();
            }
            let stem = format!("{count}-{}", u8::from(restricted));
            fs::write(directory().join(format!("{stem}.proof")), proof.as_ref()).unwrap();
            write_instances(directory().join(format!("{stem}.instances")), &instances);
        }
    }
}

#[cfg(feature = "verifier")]
#[test]
#[ignore = "run by check_orchard_backends.py in separate backend builds"]
fn verify_backend_proofs() {
    let vk = crate::cached_test_keys(OrchardCircuitVersion::PostNu6_3).verifying_key();
    for count in ACTION_COUNTS {
        for restricted in [false, true] {
            let stem = format!("{count}-{}", u8::from(restricted));
            let instances = read_instances(directory().join(format!("{stem}.instances")), count);
            let bytes = fs::read(directory().join(format!("{stem}.proof"))).unwrap();
            assert_eq!(bytes.len(), Proof::expected_proof_size(usize::from(count)));
            Proof::new(bytes.clone()).verify(vk, &instances).unwrap();
            let mut changed = bytes;
            changed[0] ^= 1;
            assert_eq!(
                Proof::new(changed).verify(vk, &instances),
                Err(ProofError::InvalidProof)
            );
        }
    }
}
