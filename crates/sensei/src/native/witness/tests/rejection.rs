//! Public/private relation rejection and enable/dummy-spend semantics.

use crate::{
    Error,
    native::field::Fp,
    types::{HEADER_SIZE, ProvingRequest},
};

// First-Action public offsets are specified by this test, independently of the
// production public-input indices.
const FIELD_SIZE: usize = 32;
const PUBLIC_START: usize = HEADER_SIZE;
const ANCHOR_START: usize = PUBLIC_START;
const CV_NET_START: usize = PUBLIC_START + FIELD_SIZE;
const NF_OLD_START: usize = PUBLIC_START + 3 * FIELD_SIZE;
const RK_START: usize = PUBLIC_START + 4 * FIELD_SIZE;
const CMX_START: usize = PUBLIC_START + 6 * FIELD_SIZE;
const DISABLE_CROSS_ADDRESS_START: usize = PUBLIC_START + 9 * FIELD_SIZE;

#[test]
fn native_nullifier_rejects_a_mismatched_public_value() {
    const FIXTURE: &[u8] = include_bytes!("../../../../tests/fixtures/one-action.iwpr");
    let mut request = FIXTURE.to_vec();
    let encoded: [u8; FIELD_SIZE] = request[NF_OLD_START..NF_OLD_START + FIELD_SIZE]
        .try_into()
        .unwrap();
    let mismatched = <Fp>::from_bytes(encoded)
        .unwrap()
        .add(&<Fp>::ONE)
        .to_bytes();
    request[NF_OLD_START..NF_OLD_START + FIELD_SIZE].copy_from_slice(&mismatched);

    let parsed = ProvingRequest::decode_iwpr_for_test(&request).unwrap();
    assert!(matches!(
        super::super::build_native_witness(&parsed.actions()[0]),
        Err(Error::InvalidStatement)
    ));
}

#[test]
fn native_commit_ivk_rejects_a_mismatched_transmission_key() {
    const FIXTURE: &[u8] = include_bytes!("../../../../tests/fixtures/one-action.iwpr");
    const PUBLIC_VALUE_COUNT: usize = 10;
    const MERKLE_DEPTH: usize = 32;
    const POSITION_SIZE: usize = 4;
    const G_D_OLD_START: usize =
        HEADER_SIZE + PUBLIC_VALUE_COUNT * FIELD_SIZE + MERKLE_DEPTH * FIELD_SIZE + POSITION_SIZE;
    const PK_D_OLD_START: usize = G_D_OLD_START + FIELD_SIZE;

    let mut request = FIXTURE.to_vec();
    let mismatched: [u8; FIELD_SIZE] = request[G_D_OLD_START..G_D_OLD_START + FIELD_SIZE]
        .try_into()
        .unwrap();
    request[PK_D_OLD_START..PK_D_OLD_START + FIELD_SIZE].copy_from_slice(&mismatched);

    let parsed = ProvingRequest::decode_iwpr_for_test(&request).unwrap();
    assert!(matches!(
        super::super::build_native_witness(&parsed.actions()[0]),
        Err(Error::UnsatisfiedWitness)
    ));
}

#[test]
fn native_note_commit_rejects_mismatched_old_randomness() {
    const FIXTURE: &[u8] = include_bytes!("../../../../tests/fixtures/one-action.iwpr");
    const PUBLIC_VALUE_COUNT: usize = 10;
    const MERKLE_DEPTH: usize = 32;
    const POSITION_SIZE: usize = 4;
    const VALUE_SIZE: usize = 8;
    const RCM_OLD_START: usize = HEADER_SIZE
        + PUBLIC_VALUE_COUNT * FIELD_SIZE
        + MERKLE_DEPTH * FIELD_SIZE
        + POSITION_SIZE
        + 2 * FIELD_SIZE
        + VALUE_SIZE
        + 2 * FIELD_SIZE;

    let mut request = FIXTURE.to_vec();
    request[RCM_OLD_START..RCM_OLD_START + FIELD_SIZE].fill(0);

    let parsed = ProvingRequest::decode_iwpr_for_test(&request).unwrap();
    assert!(matches!(
        super::super::build_native_witness(&parsed.actions()[0]),
        Err(Error::UnsatisfiedWitness)
    ));
}

#[test]
fn native_note_commit_rejects_a_mismatched_public_cmx() {
    const FIXTURE: &[u8] = include_bytes!("../../../../tests/fixtures/one-action.iwpr");

    let mut request = FIXTURE.to_vec();
    let encoded: [u8; FIELD_SIZE] = request[CMX_START..CMX_START + FIELD_SIZE]
        .try_into()
        .unwrap();
    let mismatched = <Fp>::from_bytes(encoded)
        .unwrap()
        .add(&<Fp>::ONE)
        .to_bytes();
    request[CMX_START..CMX_START + FIELD_SIZE].copy_from_slice(&mismatched);

    let parsed = ProvingRequest::decode_iwpr_for_test(&request).unwrap();
    assert!(matches!(
        super::super::build_native_witness(&parsed.actions()[0]),
        Err(Error::InvalidStatement)
    ));
}

#[test]
fn native_merkle_root_check_preserves_dummy_spend_semantics() {
    let root = <Fp>::from_u64(7);
    let anchor = <Fp>::from_u64(9);
    assert_eq!(super::super::require_merkle_root(0, &root, &anchor), Ok(()));
    assert_eq!(
        super::super::require_merkle_root(1, &root, &anchor),
        Err(Error::InvalidStatement)
    );
    assert_eq!(super::super::require_merkle_root(1, &root, &root), Ok(()));
}

#[test]
fn native_top_level_checks_preserve_enable_and_dummy_semantics() {
    assert!(super::super::top_level_relations_hold(
        0, 0, false, false, false, false
    ));
    assert!(!super::super::top_level_relations_hold(
        1, 0, false, false, false, false
    ));
    assert!(!super::super::top_level_relations_hold(
        0, 1, false, false, false, false
    ));
    assert!(!super::super::top_level_relations_hold(
        0, 0, false, false, true, false
    ));
    assert!(super::super::top_level_relations_hold(
        1, 1, true, true, true, true
    ));
}

#[test]
fn native_top_level_checks_reject_a_cross_address_action() {
    const FIXTURE: &[u8] = include_bytes!("../../../../tests/fixtures/one-action.iwpr");

    let original = ProvingRequest::decode_iwpr_for_test(FIXTURE).unwrap();
    let action = &original.actions()[0];
    assert!(
        action.witness.g_d_old != action.witness.g_d_new
            || action.witness.pk_d_old != action.witness.pk_d_new
    );
    assert!(!action.statement.disable_cross_address);

    let mut request = FIXTURE.to_vec();
    request[DISABLE_CROSS_ADDRESS_START] = 1;
    let parsed = ProvingRequest::decode_iwpr_for_test(&request).unwrap();
    assert!(matches!(
        super::super::build_native_witness(&parsed.actions()[0]),
        Err(Error::InvalidStatement)
    ));
}

#[test]
fn native_compact_rejection_corpus_fails_before_proving() {
    use crate::types::ACTION_SIZE;

    const PUBLIC_VALUE_COUNT: usize = 10;
    const MERKLE_DEPTH: usize = 32;
    const POSITION_SIZE: usize = 4;
    const VALUE_SIZE: usize = 8;
    const WITNESS_START: usize = PUBLIC_START + PUBLIC_VALUE_COUNT * FIELD_SIZE;
    const G_D_OLD_START: usize = WITNESS_START + MERKLE_DEPTH * FIELD_SIZE + POSITION_SIZE;
    const RCM_OLD_START: usize = G_D_OLD_START + 2 * FIELD_SIZE + VALUE_SIZE + 2 * FIELD_SIZE;
    const PSI_NEW_START: usize = RCM_OLD_START + 8 * FIELD_SIZE + VALUE_SIZE;
    const RCV_START: usize = PSI_NEW_START + 2 * FIELD_SIZE;

    const BASE: &[u8] = include_bytes!("../../../../tests/fixtures/one-action.iwpr");
    const BATCH: &[u8] = include_bytes!("../../../../tests/fixtures/two-action.iwpr");

    fn increment_fp(request: &mut [u8], offset: usize) {
        let encoded = request[offset..offset + FIELD_SIZE].try_into().unwrap();
        let incremented = <Fp>::from_bytes(encoded)
            .unwrap()
            .add(&<Fp>::ONE)
            .to_bytes();
        request[offset..offset + FIELD_SIZE].copy_from_slice(&incremented);
    }

    fn assert_rejected(case: &str, request: &[u8], expected: Error) {
        let parsed = ProvingRequest::decode_iwpr_for_test(request).unwrap();
        assert_eq!(
            super::super::build_native_witness_matrices(
                crate::test_codec::target(),
                crate::test_codec::execution(),
                &parsed,
                &parsed.native_statements(),
                &crate::native::prover::LookupWorkspace::default(),
            )
            .err(),
            Some(expected),
            "{case}"
        );
    }

    // The root check is conditional on a nonzero spent value, so a
    // zero-valued spend legally accepts an arbitrary anchor.
    let mut foreign_anchor = BASE.to_vec();
    increment_fp(&mut foreign_anchor, ANCHOR_START);
    let parsed = ProvingRequest::decode_iwpr_for_test(&foreign_anchor).unwrap();
    assert!(
        super::super::build_native_witness_matrices(
            crate::test_codec::target(),
            crate::test_codec::execution(),
            &parsed,
            &parsed.native_statements(),
            &crate::native::prover::LookupWorkspace::default(),
        )
        .is_ok()
    );

    let mut bad_value_commitment = BASE.to_vec();
    bad_value_commitment[CV_NET_START..CV_NET_START + 2 * FIELD_SIZE].fill(0);
    assert_rejected(
        "bad_value_commitment",
        &bad_value_commitment,
        Error::InvalidStatement,
    );

    let mut bad_nullifier = BASE.to_vec();
    increment_fp(&mut bad_nullifier, NF_OLD_START);
    assert_rejected("bad_nullifier", &bad_nullifier, Error::InvalidStatement);

    let mut bad_rk = BASE.to_vec();
    let second_action_rk = RK_START + ACTION_SIZE;
    bad_rk[RK_START..RK_START + 2 * FIELD_SIZE]
        .copy_from_slice(&BATCH[second_action_rk..second_action_rk + 2 * FIELD_SIZE]);
    assert_rejected("bad_rk", &bad_rk, Error::InvalidStatement);

    let mut bad_cmx = BASE.to_vec();
    increment_fp(&mut bad_cmx, CMX_START);
    assert_rejected("bad_cmx", &bad_cmx, Error::InvalidStatement);

    let mut bad_restricted_pairing = BASE.to_vec();
    bad_restricted_pairing[DISABLE_CROSS_ADDRESS_START] = 1;
    assert_rejected(
        "bad_restricted_pairing",
        &bad_restricted_pairing,
        Error::InvalidStatement,
    );

    let mut inconsistent_old_commitment = BASE.to_vec();
    inconsistent_old_commitment[RCM_OLD_START..RCM_OLD_START + FIELD_SIZE].fill(0);
    assert_rejected(
        "inconsistent_old_commitment",
        &inconsistent_old_commitment,
        Error::UnsatisfiedWitness,
    );

    let mut inconsistent_output = BASE.to_vec();
    increment_fp(&mut inconsistent_output, PSI_NEW_START);
    assert_rejected(
        "inconsistent_output",
        &inconsistent_output,
        Error::InvalidStatement,
    );

    let mut bad_value_blind = BASE.to_vec();
    bad_value_blind[RCV_START..RCV_START + FIELD_SIZE].fill(0);
    assert_rejected("bad_value_blind", &bad_value_blind, Error::InvalidStatement);
}
