//! Compatibility against independently generated, immutable pre-migration fixtures.
use super::*;
use crate::backend::pallas;
#[cfg(feature = "backend-halo2")]
use crate::backend::prelude::*;
use crate::bundle::{BundleError, BundleVersion, validate_proof_size};

/// Each stored fixture authorizes exactly one action.
const FIXTURE_ACTIONS: usize = 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProofFixtureEncoding {
    LegacyTwoFlags,
    PostNu6_3ThreeFlags,
}

fn read_test_case<R: std::io::Read>(
    mut r: R,
    encoding: ProofFixtureEncoding,
) -> std::io::Result<(Instance, Proof)> {
    let read_32_bytes = |r: &mut R| {
        let mut ret = [0u8; 32];
        r.read_exact(&mut ret).unwrap();
        ret
    };
    let read_bool = |r: &mut R| {
        let mut byte = [0u8; 1];
        r.read_exact(&mut byte).unwrap();
        match byte {
            [0] => false,
            [1] => true,
            _ => panic!("Unexpected non-boolean byte"),
        }
    };

    let anchor = crate::Anchor::from_bytes(read_32_bytes(&mut r)).unwrap();
    let cv_net = ValueCommitment::from_bytes(&read_32_bytes(&mut r)).unwrap();
    let nf_old = crate::note::Nullifier::from_bytes(&read_32_bytes(&mut r)).unwrap();
    let rk = read_32_bytes(&mut r).try_into().unwrap();
    let cmx = crate::note::ExtractedNoteCommitment::from_bytes(&read_32_bytes(&mut r)).unwrap();
    let enable_spend = read_bool(&mut r);
    let enable_output = read_bool(&mut r);
    let (cross_address_bit, bundle_version) = match encoding {
        ProofFixtureEncoding::LegacyTwoFlags => (0, BundleVersion::orchard_v2()),
        ProofFixtureEncoding::PostNu6_3ThreeFlags => {
            // The fixture stores the instance-level *disable* bit; the NU6.3 flag
            // byte carries the *enable* bit, so invert when reconstructing.
            //
            // The circuit is pool-agnostic; decode under Ironwood, the pool whose flag
            // byte can represent `enableCrossAddress` either way (Orchard post-NU6.3
            // rejects bit 2).
            let cross_address_disabled = read_bool(&mut r);
            (
                u8::from(!cross_address_disabled) << 2,
                BundleVersion::ironwood_v3(),
            )
        }
    };
    let flags = Flags::from_byte(
        u8::from(enable_spend) | (u8::from(enable_output) << 1) | cross_address_bit,
        bundle_version,
    )
    .expect("test vectors use canonical flag encodings");

    let instance = Instance::from_parts(anchor, cv_net, nf_old, rk, cmx, flags)
        .expect("test vectors were generated with non-identity rk");

    let mut proof_bytes = vec![];
    r.read_to_end(&mut proof_bytes)?;
    let proof = Proof::new(proof_bytes);

    Ok((instance, proof))
}

/// Fingerprints of the three pinned circuit descriptions. Computed as
/// BLAKE2b-256(person="Orchard-VkFprint") over the fixture files; a change here
/// means the verifying key changed.
#[test]
fn verifying_key_fingerprints_are_pinned() {
    let expect = |hex: &str| -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, b) in out.iter_mut().enumerate() {
            *b = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    };
    for (version, hex) in [
        (
            OrchardCircuitVersion::InsecurePreNu6_2,
            "6e6df0842e34ccdf251813ce52e1db353e03b0330ccb64ce8fa1cf9b3cfef6ce",
        ),
        (
            OrchardCircuitVersion::FixedPostNu6_2,
            "1bee049ad3ff027c8d448e64b4413b3c4a483a743b5f39bcfbb6102f626591fb",
        ),
        (
            OrchardCircuitVersion::PostNu6_3,
            "3409b1d4c3e45906d283bdf402fdc61a3eb22b2ff72b25943a738d0e4558ab72",
        ),
    ] {
        let vk = VerifyingKey::build(version);
        assert_eq!(vk.fingerprint(), expect(hex), "{version:?}");
    }
}

#[test]
fn stored_proofs_verify_only_for_their_version() {
    let versions = [
        OrchardCircuitVersion::InsecurePreNu6_2,
        OrchardCircuitVersion::FixedPostNu6_2,
        OrchardCircuitVersion::PostNu6_3,
    ];
    for (version, bytes, encoding) in [
        (
            versions[0],
            include_bytes!("../circuit_data/circuit_proof_test_case_insecure.bin").as_slice(),
            ProofFixtureEncoding::LegacyTwoFlags,
        ),
        (
            versions[1],
            include_bytes!("../circuit_data/circuit_proof_test_case_fixed.bin").as_slice(),
            ProofFixtureEncoding::LegacyTwoFlags,
        ),
        (
            versions[2],
            include_bytes!("../circuit_data/circuit_proof_test_case_post_nu6_3.bin").as_slice(),
            ProofFixtureEncoding::PostNu6_3ThreeFlags,
        ),
        (
            versions[2],
            include_bytes!("../circuit_data/circuit_proof_test_case_post_nu6_3_restricted.bin")
                .as_slice(),
            ProofFixtureEncoding::PostNu6_3ThreeFlags,
        ),
    ] {
        let (instance, proof) = read_test_case(bytes, encoding).unwrap();
        for verification_version in versions {
            let key = VerifyingKey::build(verification_version);
            assert_eq!(
                proof.verify(&key, core::slice::from_ref(&instance)).is_ok(),
                version == verification_version
            );
        }
        let key = VerifyingKey::build(version);
        // The pre-migration proofs pin the canonical length, and the bundle constructors'
        // length check is what rejects padding: `Proof::verify` reads the canonical proof
        // and ignores trailing bytes.
        let expected = Proof::expected_proof_size(FIXTURE_ACTIONS);
        assert_eq!(proof.0.len(), expected);
        assert_eq!(validate_proof_size(&proof, FIXTURE_ACTIONS), Ok(()));
        let mut malformed = proof.clone();
        malformed.0.push(0);
        assert_eq!(
            validate_proof_size(&malformed, FIXTURE_ACTIONS),
            Err(BundleError::NonCanonicalProofSize {
                expected,
                actual: expected + 1,
            })
        );
        malformed = proof.clone();
        malformed.0.pop();
        assert_eq!(
            malformed.verify(&key, core::slice::from_ref(&instance)),
            Err(ProofError::InvalidProof)
        );
        malformed = proof.clone();
        malformed.0[0] ^= 1;
        assert_eq!(
            malformed.verify(&key, core::slice::from_ref(&instance)),
            Err(ProofError::InvalidProof)
        );
        let mut different = instance.clone();
        different.cmx = ExtractedNoteCommitment::from_bytes(
            &(instance.cmx.inner() + pallas::Base::from(1)).to_repr(),
        )
        .unwrap();
        assert_eq!(
            proof.verify(&key, &[different]),
            Err(ProofError::InvalidProof)
        );
        if !version.supports_cross_address_restriction() {
            let mut restricted = instance;
            restricted.cross_address_disabled = true;
            assert_eq!(
                proof.verify(&key, &[restricted]),
                Err(ProofError::InvalidInput)
            );
        }
    }
}
