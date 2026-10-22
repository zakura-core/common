use proptest::prelude::*;

#[cfg(test)]
use {
    crate::transaction::{
        Authorization, Authorized, Transaction, TransactionData, TxDigests, TxIn, TxVersion,
        sighash::{PrecomputedSighashData, SignableInput, Zip244Error, signature_hash},
        sighash_v4::{v4_signature_hash, v4_signature_hash_with_digests, zip143_digests},
        sighash_v5::v5_signature_hash,
        testing::arb_tx,
        transparent,
        txid::TxIdDigester,
    },
    ::transparent::{
        address::Script, sighash::SighashType, sighash::TransparentAuthorizingContext,
    },
    alloc::vec::Vec,
    blake2b_simd::Hash as Blake2bHash,
    core::{cell::Cell, ops::Deref},
    zcash_protocol::{consensus::BranchId, value::Zatoshis},
    zcash_script::script,
};

#[cfg(test)]
use crate::transaction::{
    TransactionDigest,
    txid::{BlockTxCommitmentDigester, hash_sapling_spends},
};

#[cfg(test)]
use crate::transaction::sighash_v6::v6_signature_hash;

#[cfg(test)]
use blake2b_simd::Params;

#[cfg(test)]
use ff::PrimeField;

#[cfg(test)]
use zcash_protocol::value::ZatBalance;

#[cfg(any(test, feature = "test-dependencies"))]
pub mod data;

#[test]
fn tx_read_write() {
    let data = &self::data::tx_read_write::TX_READ_WRITE;
    let tx = Transaction::read(&data[..], BranchId::Canopy).unwrap();
    assert_eq!(
        format!("{}", tx.txid()),
        "64f0bd7fe30ce23753358fe3a2dc835b8fba9c0274c4e2c54a6f73114cb55639"
    );

    let mut encoded = Vec::with_capacity(data.len());
    tx.write(&mut encoded).unwrap();
    assert_eq!(&data[..], &encoded[..]);
}

#[test]
fn v6_encoding_hashes_and_fee_are_independent_of_nu7_cfg() {
    // Synthetic transparent transaction with a 20-byte ZIP 229 header.
    // Expected hashes were computed independently with Python hashlib.blake2b,
    // using the ZIP 244 digest tree and the V6 shielded personalizations.
    let bytes = hex::decode("0600008098b684d85b16a53701000000020000000100000000000000000000000000000000000000000000000000000000000000000000000000ffffffff0150c3000000000000015100000000").unwrap();
    let tx = Transaction::read(&bytes[..], BranchId::Nu6_3).unwrap();

    let mut header = Vec::new();
    tx.write_v6_header(&mut header).unwrap();
    assert_eq!(header, bytes[..20]);
    assert_eq!(tx.lock_time(), 1);
    assert_eq!(u32::from(tx.expiry_height()), 2);
    assert_eq!(tx.transparent_bundle().unwrap().vin.len(), 1);
    assert_eq!(tx.transparent_bundle().unwrap().vout.len(), 1);

    let mut encoded = Vec::new();
    tx.write(&mut encoded).unwrap();
    assert_eq!(encoded, bytes);
    assert_eq!(
        hex::encode(tx.txid().as_ref()),
        "e11e16887d9aea199fc4eaa3b371c6868ded3e9a2b1c3393a7b0c15f79e73179"
    );
    assert_eq!(
        hex::encode(tx.auth_commitment().as_bytes()),
        "454423cf6de9acb289a60852144679176cea3bd5e5ec51526d483ced2533e73a"
    );
    assert_eq!(
        hex::encode(tx.digest(TxIdDigester).header_digest.as_bytes()),
        "434bc31eb5d67ac6b935ab85cb0aabc06b079c39f8f4e1b50a6048372b3bfa2d"
    );
    assert_eq!(
        tx.fee_paid(|_| Ok::<_, zcash_protocol::value::BalanceError>(Some(
            Zatoshis::const_from_u64(65_000)
        )))
        .unwrap(),
        Some(Zatoshis::const_from_u64(15_000))
    );
}

#[test]
fn suggested_version_for_v5_branches_is_not_v6() {
    assert_eq!(
        TxVersion::suggested_for_branch(BranchId::Nu5),
        TxVersion::V5
    );
    assert_eq!(
        TxVersion::suggested_for_branch(BranchId::Nu6),
        TxVersion::V5
    );
    assert_eq!(
        TxVersion::suggested_for_branch(BranchId::Nu6_1),
        TxVersion::V5
    );
}

#[cfg(test)]
#[test]
fn v4_transactions_remain_valid_in_nu6_3() {
    assert!(TxVersion::V4.valid_in_branch(BranchId::Nu6_3));
}

#[cfg(test)]
#[test]
fn v5_auth_commitment_in_nu6_3_does_not_include_ironwood_digest() {
    fn empty_hash(personal: &[u8; 16]) -> Blake2bHash {
        Params::new().hash_length(32).personal(personal).hash(&[])
    }

    let mut personal = [0; 16];
    personal[..12].copy_from_slice(b"ZTxAuthHash_");
    personal[12..].copy_from_slice(&u32::from(BranchId::Nu6_3).to_le_bytes());

    let mut expected = Params::new().hash_length(32).personal(&personal).to_state();
    expected.update(empty_hash(b"ZTxAuthTransHash").as_bytes());
    expected.update(empty_hash(b"ZTxAuthSapliHash").as_bytes());
    expected.update(empty_hash(b"ZTxAuthOrchaHash").as_bytes());

    let tx = TransactionData::from_parts(
        TxVersion::V5,
        BranchId::Nu6_3,
        0,
        0u32.into(),
        None,
        None,
        None,
        None,
    )
    .freeze()
    .unwrap();

    assert_eq!(tx.auth_commitment(), expected.finalize());
}

#[cfg(test)]
#[test]
fn v6_empty_auth_commitment_uses_v6_shielded_personalizations() {
    fn empty_hash(personal: &[u8; 16]) -> Blake2bHash {
        Params::new().hash_length(32).personal(personal).hash(&[])
    }

    let mut personal = [0; 16];
    personal[..12].copy_from_slice(b"ZTxAuthHash_");
    personal[12..].copy_from_slice(&u32::from(BranchId::Nu6_3).to_le_bytes());

    let mut expected = Params::new().hash_length(32).personal(&personal).to_state();
    expected.update(empty_hash(b"ZTxAuthTransHash").as_bytes());
    expected.update(empty_hash(b"ZTxAuthSapliH_v6").as_bytes());
    expected.update(empty_hash(b"ZTxAuthOrchaH_v6").as_bytes());
    expected.update(empty_hash(b"ZTxAuthIrnwdH_v6").as_bytes());

    let tx =
        TransactionData::from_parts_v6(BranchId::Nu6_3, 0, 0u32.into(), None, None, None, None)
            .freeze()
            .unwrap();

    assert_eq!(tx.auth_commitment(), expected.finalize());
}

#[cfg(test)]
#[test]
fn v6_empty_orchard_txid_uses_v6_orchard_personalization() {
    fn empty_hash(personal: &[u8; 16]) -> Blake2bHash {
        Params::new().hash_length(32).personal(personal).hash(&[])
    }

    let tx_data =
        TransactionData::from_parts_v6(BranchId::Nu6_3, 0, 0u32.into(), None, None, None, None);
    let txid_parts = tx_data.digest(TxIdDigester);
    let tx = tx_data.freeze().unwrap();

    assert!(txid_parts.orchard_digest.is_none());
    assert!(txid_parts.ironwood_digest.is_none());

    let mut personal = [0; 16];
    personal[..12].copy_from_slice(b"ZcashTxHash_");
    personal[12..].copy_from_slice(&u32::from(BranchId::Nu6_3).to_le_bytes());

    let mut expected = Params::new().hash_length(32).personal(&personal).to_state();
    expected.update(txid_parts.header_digest.as_bytes());
    expected.update(empty_hash(b"ZTxIdTranspaHash").as_bytes());
    expected.update(empty_hash(b"ZTxIdSaplingHash").as_bytes());
    expected.update(empty_hash(b"ZTxIdOrchardH_v6").as_bytes());
    expected.update(empty_hash(b"ZTxIdIronwd_H_v6").as_bytes());

    let expected = expected.finalize();
    assert_eq!(&tx.txid().as_ref()[..], expected.as_bytes());
}

#[cfg(test)]
#[test]
fn v6_branch_reconstruction_preserves_ironwood_bundle() {
    use proptest::test_runner::TestRunner;

    let mut runner = TestRunner::default();
    let ironwood_bundle = test_ironwood_bundle(&mut runner);
    let tx = TransactionData::from_parts_v6(
        BranchId::Nu6_3,
        0,
        1u32.into(),
        None,
        None,
        None,
        Some(ironwood_bundle),
    )
    .freeze()
    .unwrap();

    let original_txid = tx.txid();
    let mut tx_bytes = vec![];
    tx.write(&mut tx_bytes).unwrap();

    let tx_data = Transaction::read(&tx_bytes[..], BranchId::Sprout)
        .unwrap()
        .into_data();

    let legacy_rebuilt = TransactionData::from_parts(
        tx_data.version(),
        tx_data.consensus_branch_id(),
        tx_data.lock_time(),
        tx_data.expiry_height(),
        tx_data.transparent_bundle().cloned(),
        tx_data.sprout_bundle().cloned(),
        tx_data.sapling_bundle().cloned(),
        tx_data.orchard_bundle().cloned(),
    )
    .freeze()
    .unwrap();
    assert!(legacy_rebuilt.ironwood_bundle().is_none());
    assert_ne!(legacy_rebuilt.txid(), original_txid);

    let rebuilt = TransactionData::from_parts_v6(
        tx_data.consensus_branch_id(),
        tx_data.lock_time(),
        tx_data.expiry_height(),
        tx_data.transparent_bundle().cloned(),
        tx_data.sapling_bundle().cloned(),
        tx_data.orchard_bundle().cloned(),
        tx_data.ironwood_bundle().cloned(),
    )
    .freeze()
    .unwrap();

    assert!(rebuilt.ironwood_bundle().is_some());
    assert_eq!(rebuilt.txid(), original_txid);
}

#[cfg(test)]
fn test_anchor(byte: u8) -> orchard::Anchor {
    let mut bytes = [0u8; 32];
    bytes[0] = byte;
    orchard::Anchor::from_bytes(bytes).unwrap()
}

#[cfg(test)]
fn test_orchard_bundle(
    runner: &mut proptest::test_runner::TestRunner,
) -> orchard::Bundle<orchard::bundle::Authorized, ZatBalance> {
    use proptest::strategy::ValueTree;

    let bundle = crate::transaction::components::orchard::testing::arb_bundle(1)
        .new_tree(runner)
        .unwrap()
        .current();
    crate::transaction::components::orchard::testing::rebuild_with_version(
        bundle,
        orchard::bundle::BundleVersion::orchard_v3(),
    )
}

#[cfg(test)]
fn test_ironwood_bundle(
    runner: &mut proptest::test_runner::TestRunner,
) -> orchard::Bundle<orchard::bundle::Authorized, ZatBalance> {
    use proptest::strategy::ValueTree;

    let bundle = crate::transaction::components::orchard::testing::arb_bundle(1)
        .new_tree(runner)
        .unwrap()
        .current();
    crate::transaction::components::orchard::testing::rebuild_with_version(
        bundle,
        orchard::bundle::BundleVersion::ironwood_v3(),
    )
}

#[cfg(test)]
fn bundle_with_anchor(
    bundle: &orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
    anchor: orchard::Anchor,
) -> orchard::Bundle<orchard::bundle::Authorized, ZatBalance> {
    orchard::Bundle::try_from_parts(
        bundle.actions().clone(),
        *bundle.flags(),
        *bundle.value_balance(),
        anchor,
        bundle.authorization().clone(),
        bundle.bundle_version(),
    )
    .unwrap()
}

#[cfg(test)]
fn test_sapling_anchor(byte: u8) -> bls12_381::Scalar {
    bls12_381::Scalar::from(u64::from(byte))
}

#[cfg(test)]
fn test_sapling_bundle(
    runner: &mut proptest::test_runner::TestRunner,
) -> sapling::Bundle<sapling::bundle::Authorized, ZatBalance> {
    use proptest::strategy::ValueTree;

    let bundle_strategy =
        crate::transaction::components::sapling::testing::arb_bundle_for_version(TxVersion::V6);

    for _ in 0..100 {
        if let Some(bundle) = bundle_strategy.new_tree(runner).unwrap().current()
            && !bundle.shielded_spends().is_empty()
        {
            return bundle;
        }
    }

    panic!("Sapling bundle strategy should generate a bundle with spends");
}

#[cfg(test)]
fn test_sapling_output_only_bundle(
    runner: &mut proptest::test_runner::TestRunner,
) -> sapling::Bundle<sapling::bundle::Authorized, ZatBalance> {
    use proptest::strategy::ValueTree;

    let bundle_strategy =
        crate::transaction::components::sapling::testing::arb_bundle_for_version(TxVersion::V6);

    for _ in 0..1000 {
        if let Some(bundle) = bundle_strategy.new_tree(runner).unwrap().current()
            && bundle.shielded_spends().is_empty()
            && !bundle.shielded_outputs().is_empty()
        {
            return bundle;
        }
    }

    panic!("Sapling bundle strategy should generate an output-only bundle");
}

#[cfg(test)]
fn sapling_bundle_with_anchor(
    bundle: &sapling::Bundle<sapling::bundle::Authorized, ZatBalance>,
    anchor: bls12_381::Scalar,
) -> sapling::Bundle<sapling::bundle::Authorized, ZatBalance> {
    let spends = bundle
        .shielded_spends()
        .iter()
        .map(|spend| {
            sapling::bundle::SpendDescription::from_parts(
                spend.cv().clone(),
                anchor,
                *spend.nullifier(),
                *spend.rk(),
                *spend.zkproof(),
                *spend.spend_auth_sig(),
            )
        })
        .collect();

    sapling::Bundle::from_parts(
        spends,
        bundle.shielded_outputs().to_vec(),
        *bundle.value_balance(),
        *bundle.authorization(),
    )
    .expect("test bundle has Sapling spends")
}

#[cfg(test)]
fn tx_bytes(tx: &Transaction) -> Vec<u8> {
    let mut encoded = Vec::new();
    tx.write(&mut encoded).unwrap();
    encoded
}

#[cfg(test)]
fn v5_tx_with_orchard_bundle(
    orchard_bundle: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
) -> Transaction {
    TransactionData::<crate::transaction::Authorized>::from_parts(
        TxVersion::V5,
        BranchId::Nu5,
        0,
        1u32.into(),
        None,
        None,
        None,
        Some(orchard_bundle),
    )
    .freeze()
    .unwrap()
}

#[cfg(test)]
fn v5_tx_data_with_orchard_bundle(
    orchard_bundle: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
) -> TransactionData<TestUnauthorized> {
    TransactionData::from_parts(
        TxVersion::V5,
        BranchId::Nu5,
        0,
        1u32.into(),
        None,
        None,
        None,
        Some(orchard_bundle),
    )
}

#[cfg(test)]
fn v5_tx_with_sapling_bundle(
    sapling_bundle: sapling::Bundle<sapling::bundle::Authorized, ZatBalance>,
) -> Transaction {
    TransactionData::<crate::transaction::Authorized>::from_parts(
        TxVersion::V5,
        BranchId::Nu5,
        0,
        1u32.into(),
        None,
        None,
        Some(sapling_bundle),
        None,
    )
    .freeze()
    .unwrap()
}

#[cfg(test)]
fn v5_tx_data_with_sapling_bundle(
    sapling_bundle: sapling::Bundle<sapling::bundle::Authorized, ZatBalance>,
) -> TransactionData<TestUnauthorized> {
    TransactionData::from_parts(
        TxVersion::V5,
        BranchId::Nu5,
        0,
        1u32.into(),
        None,
        None,
        Some(sapling_bundle),
        None,
    )
}

/// Clears the cross-address flag on an Orchard bundle (preserving spends/outputs)
/// so it is representable in a v6 Orchard slot ([`orchard::bundle::BundleVersion::orchard_v3`],
/// which forbids cross-address transfers; cross-address is Ironwood-only).
#[cfg(test)]
fn disable_cross_address(
    bundle: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
) -> orchard::Bundle<orchard::bundle::Authorized, ZatBalance> {
    let byte = u8::from(bundle.flags().spends_enabled())
        | (u8::from(bundle.flags().outputs_enabled()) << 1);
    let flags =
        orchard::bundle::Flags::from_byte(byte, orchard::bundle::BundleVersion::orchard_v3())
            .unwrap();
    orchard::Bundle::try_from_parts(
        bundle.actions().clone(),
        flags,
        *bundle.value_balance(),
        *bundle.anchor(),
        bundle.authorization().clone(),
        orchard::bundle::BundleVersion::orchard_v3(),
    )
    .unwrap()
}

#[cfg(test)]
fn v6_tx_with_orchard_bundle(
    orchard_bundle: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
) -> Transaction {
    TransactionData::<crate::transaction::Authorized>::from_parts_v6(
        BranchId::Nu6_3,
        0,
        1u32.into(),
        None,
        None,
        Some(disable_cross_address(orchard_bundle)),
        None,
    )
    .freeze()
    .unwrap()
}

#[cfg(test)]
fn v6_tx_with_sapling_bundle(
    sapling_bundle: sapling::Bundle<sapling::bundle::Authorized, ZatBalance>,
) -> Transaction {
    TransactionData::<crate::transaction::Authorized>::from_parts_v6(
        BranchId::Nu6_3,
        0,
        1u32.into(),
        None,
        Some(sapling_bundle),
        None,
        None,
    )
    .freeze()
    .unwrap()
}

#[cfg(test)]
fn v6_tx_data_with_sapling_bundle(
    sapling_bundle: sapling::Bundle<sapling::bundle::Authorized, ZatBalance>,
) -> TransactionData<TestUnauthorized> {
    TransactionData::from_parts_v6(
        BranchId::Nu6_3,
        0,
        1u32.into(),
        None,
        Some(sapling_bundle),
        None,
        None,
    )
}

#[cfg(test)]
fn v6_tx_data_with_orchard_bundle(
    orchard_bundle: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
) -> TransactionData<TestUnauthorized> {
    TransactionData::from_parts_v6(
        BranchId::Nu6_3,
        0,
        1u32.into(),
        None,
        None,
        Some(disable_cross_address(orchard_bundle)),
        None,
    )
}

#[cfg(test)]
fn v6_tx_with_ironwood_bundle(
    ironwood_bundle: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
) -> Transaction {
    TransactionData::<crate::transaction::Authorized>::from_parts_v6(
        BranchId::Nu6_3,
        0,
        1u32.into(),
        None,
        None,
        None,
        Some(ironwood_bundle),
    )
    .freeze()
    .unwrap()
}

#[cfg(test)]
fn v6_tx_data_with_ironwood_bundle(
    ironwood_bundle: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
) -> TransactionData<TestUnauthorized> {
    TransactionData::from_parts_v6(
        BranchId::Nu6_3,
        0,
        1u32.into(),
        None,
        None,
        None,
        Some(ironwood_bundle),
    )
}

#[cfg(test)]
fn v5_shielded_sighash(tx_data: &TransactionData<TestUnauthorized>) -> Blake2bHash {
    let txid_parts = tx_data.digest(TxIdDigester);
    v5_signature_hash(tx_data, &SignableInput::Shielded, &txid_parts)
}

#[cfg(test)]
fn v6_shielded_sighash(tx_data: &TransactionData<TestUnauthorized>) -> Blake2bHash {
    let txid_parts = tx_data.digest(TxIdDigester);
    v6_signature_hash(tx_data, &SignableInput::Shielded, &txid_parts)
}

#[cfg(test)]
#[test]
fn v6_orchard_anchor_changes_auth_commitment_not_txid_or_sighash() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let bundle = test_orchard_bundle(&mut runner);

    let bundle_a = bundle_with_anchor(&bundle, test_anchor(1));
    let bundle_b = bundle_with_anchor(&bundle, test_anchor(2));
    let tx_data_a = v6_tx_data_with_orchard_bundle(bundle_a.clone());
    let tx_data_b = v6_tx_data_with_orchard_bundle(bundle_b.clone());
    let tx_a = v6_tx_with_orchard_bundle(bundle_a);
    let tx_b = v6_tx_with_orchard_bundle(bundle_b);

    assert_ne!(tx_bytes(&tx_a), tx_bytes(&tx_b));
    assert_eq!(tx_a.txid(), tx_b.txid());
    assert_eq!(
        v6_shielded_sighash(&tx_data_a),
        v6_shielded_sighash(&tx_data_b)
    );
    assert_ne!(tx_a.auth_commitment(), tx_b.auth_commitment());
}

#[cfg(test)]
#[test]
fn v6_ironwood_anchor_changes_auth_commitment_not_txid_or_sighash() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let bundle = test_ironwood_bundle(&mut runner);

    let bundle_a = bundle_with_anchor(&bundle, test_anchor(1));
    let bundle_b = bundle_with_anchor(&bundle, test_anchor(2));
    let tx_data_a = v6_tx_data_with_ironwood_bundle(bundle_a.clone());
    let tx_data_b = v6_tx_data_with_ironwood_bundle(bundle_b.clone());
    let tx_a = v6_tx_with_ironwood_bundle(bundle_a);
    let tx_b = v6_tx_with_ironwood_bundle(bundle_b);

    assert_ne!(tx_bytes(&tx_a), tx_bytes(&tx_b));
    assert_eq!(tx_a.txid(), tx_b.txid());
    assert_eq!(
        v6_shielded_sighash(&tx_data_a),
        v6_shielded_sighash(&tx_data_b)
    );
    assert_ne!(tx_a.auth_commitment(), tx_b.auth_commitment());
}

#[cfg(test)]
#[test]
fn v5_orchard_anchor_still_changes_txid_and_sighash() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let bundle = test_orchard_bundle(&mut runner);

    let bundle_a = bundle_with_anchor(&bundle, test_anchor(1));
    let bundle_b = bundle_with_anchor(&bundle, test_anchor(2));
    let tx_data_a = v5_tx_data_with_orchard_bundle(bundle_a.clone());
    let tx_data_b = v5_tx_data_with_orchard_bundle(bundle_b.clone());
    let tx_a = v5_tx_with_orchard_bundle(bundle_a);
    let tx_b = v5_tx_with_orchard_bundle(bundle_b);

    assert_ne!(tx_a.txid(), tx_b.txid());
    assert_ne!(
        v5_shielded_sighash(&tx_data_a),
        v5_shielded_sighash(&tx_data_b)
    );
    assert_eq!(tx_a.auth_commitment(), tx_b.auth_commitment());
}

#[cfg(test)]
#[test]
fn v6_sapling_anchor_changes_auth_commitment_not_txid_or_sighash() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let bundle = test_sapling_bundle(&mut runner);

    let bundle_a = sapling_bundle_with_anchor(&bundle, test_sapling_anchor(1));
    let bundle_b = sapling_bundle_with_anchor(&bundle, test_sapling_anchor(2));
    let tx_data_a = v6_tx_data_with_sapling_bundle(bundle_a.clone());
    let tx_data_b = v6_tx_data_with_sapling_bundle(bundle_b.clone());
    let tx_a = v6_tx_with_sapling_bundle(bundle_a);
    let tx_b = v6_tx_with_sapling_bundle(bundle_b);

    assert_ne!(tx_bytes(&tx_a), tx_bytes(&tx_b));
    assert_eq!(tx_a.txid(), tx_b.txid());
    assert_eq!(
        v6_shielded_sighash(&tx_data_a),
        v6_shielded_sighash(&tx_data_b)
    );
    assert_ne!(tx_a.auth_commitment(), tx_b.auth_commitment());
}

#[cfg(test)]
#[test]
fn v5_sapling_anchor_still_changes_txid_and_sighash() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let bundle = test_sapling_bundle(&mut runner);

    let bundle_a = sapling_bundle_with_anchor(&bundle, test_sapling_anchor(1));
    let bundle_b = sapling_bundle_with_anchor(&bundle, test_sapling_anchor(2));
    let tx_data_a = v5_tx_data_with_sapling_bundle(bundle_a.clone());
    let tx_data_b = v5_tx_data_with_sapling_bundle(bundle_b.clone());
    let tx_a = v5_tx_with_sapling_bundle(bundle_a);
    let tx_b = v5_tx_with_sapling_bundle(bundle_b);

    assert_ne!(tx_a.txid(), tx_b.txid());
    assert_ne!(
        v5_shielded_sighash(&tx_data_a),
        v5_shielded_sighash(&tx_data_b)
    );
    assert_eq!(tx_a.auth_commitment(), tx_b.auth_commitment());
}

#[cfg(test)]
#[test]
fn v6_sapling_spends_digest_uses_v6_noncompact_domain_without_anchor() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let bundle = test_sapling_bundle(&mut runner);

    let mut h = Params::new()
        .hash_length(32)
        .personal(b"ZTxIdSSpendsHash")
        .to_state();
    let mut ch = Params::new()
        .hash_length(32)
        .personal(b"ZTxIdSSpendCHash")
        .to_state();
    let mut nh = Params::new()
        .hash_length(32)
        .personal(b"ZTxIdSSpendNH_v6")
        .to_state();

    for spend in bundle.shielded_spends() {
        ch.update(spend.nullifier().as_ref());
        nh.update(&spend.cv().to_bytes());
        nh.update(&<[u8; 32]>::from(*spend.rk()));
    }

    h.update(ch.finalize().as_bytes());
    h.update(nh.finalize().as_bytes());

    assert_eq!(
        hash_sapling_spends(TxVersion::V6, bundle.shielded_spends()),
        h.finalize()
    );

    let bundle_a = sapling_bundle_with_anchor(&bundle, test_sapling_anchor(1));
    let bundle_b = sapling_bundle_with_anchor(&bundle, test_sapling_anchor(2));
    assert_eq!(
        hash_sapling_spends(TxVersion::V6, bundle_a.shielded_spends()),
        hash_sapling_spends(TxVersion::V6, bundle_b.shielded_spends())
    );
}

#[cfg(test)]
#[test]
fn v6_sapling_auth_digest_uses_v6_domain_and_appends_anchor() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let bundle = test_sapling_bundle(&mut runner);

    let mut h = Params::new()
        .hash_length(32)
        .personal(b"ZTxAuthSapliH_v6")
        .to_state();
    for spend in bundle.shielded_spends() {
        h.update(spend.zkproof());
    }
    for spend in bundle.shielded_spends() {
        h.update(&<[u8; 64]>::from(*spend.spend_auth_sig()));
    }
    for output in bundle.shielded_outputs() {
        h.update(output.zkproof());
    }
    h.update(&<[u8; 64]>::from(bundle.authorization().binding_sig));
    h.update(bundle.shielded_spends()[0].anchor().to_repr().as_ref());

    let actual = TransactionDigest::<crate::transaction::Authorized>::digest_sapling(
        &BlockTxCommitmentDigester,
        TxVersion::V6,
        Some(&bundle),
    );

    assert_eq!(actual, h.finalize());
}

#[cfg(test)]
#[test]
fn v6_sapling_output_only_auth_digest_uses_v6_domain_without_anchor() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let bundle = test_sapling_output_only_bundle(&mut runner);

    let mut h = Params::new()
        .hash_length(32)
        .personal(b"ZTxAuthSapliH_v6")
        .to_state();
    for output in bundle.shielded_outputs() {
        h.update(output.zkproof());
    }
    h.update(&<[u8; 64]>::from(bundle.authorization().binding_sig));

    let actual = TransactionDigest::<crate::transaction::Authorized>::digest_sapling(
        &BlockTxCommitmentDigester,
        TxVersion::V6,
        Some(&bundle),
    );

    assert_eq!(actual, h.finalize());
}

#[cfg(test)]
#[test]
fn v6_orchard_non_anchor_bundle_data_still_changes_txid_and_sighash() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let anchor = test_anchor(1);

    let bundle_a = bundle_with_anchor(&test_orchard_bundle(&mut runner), anchor);
    let bundle_b = bundle_with_anchor(&test_orchard_bundle(&mut runner), anchor);
    let tx_data_a = v6_tx_data_with_orchard_bundle(bundle_a.clone());
    let tx_data_b = v6_tx_data_with_orchard_bundle(bundle_b.clone());
    let tx_a = v6_tx_with_orchard_bundle(bundle_a);
    let tx_b = v6_tx_with_orchard_bundle(bundle_b);

    assert_ne!(tx_a.txid(), tx_b.txid());
    assert_ne!(
        v6_shielded_sighash(&tx_data_a),
        v6_shielded_sighash(&tx_data_b)
    );
    assert_ne!(tx_a.auth_commitment(), tx_b.auth_commitment());
}

#[cfg(test)]
fn check_roundtrip(tx: Transaction) -> Result<(), TestCaseError> {
    let mut txn_bytes = vec![];
    tx.write(&mut txn_bytes).unwrap();
    let txo = Transaction::read(&txn_bytes[..], tx.consensus_branch_id).unwrap();

    prop_assert_eq!(tx.version, txo.version);
    prop_assert_eq!(tx.lock_time, txo.lock_time);
    prop_assert_eq!(
        tx.transparent_bundle.as_ref(),
        txo.transparent_bundle.as_ref()
    );
    prop_assert_eq!(tx.sapling_value_balance(), txo.sapling_value_balance());
    prop_assert_eq!(
        tx.orchard_bundle.as_ref().map(|v| *v.value_balance()),
        txo.orchard_bundle.as_ref().map(|v| *v.value_balance())
    );
    #[cfg(test)]
    prop_assert_eq!(
        tx.ironwood_bundle.as_ref().map(|v| *v.value_balance()),
        txo.ironwood_bundle.as_ref().map(|v| *v.value_balance())
    );
    Ok(())
}

proptest! {
    #[test]
    #[cfg(all(feature = "expensive-tests", not(feature = "no-expensive-tests")))]
    fn tx_serialization_roundtrip_sprout(tx in arb_tx(BranchId::Sprout)) {
        check_roundtrip(tx)?;
    }
}

proptest! {
    #[test]
    #[cfg(all(feature = "expensive-tests", not(feature = "no-expensive-tests")))]
    fn tx_serialization_roundtrip_overwinter(tx in arb_tx(BranchId::Overwinter)) {
        check_roundtrip(tx)?;
    }
}

proptest! {
    #[test]
    #[cfg(all(feature = "expensive-tests", not(feature = "no-expensive-tests")))]
    fn tx_serialization_roundtrip_sapling(tx in arb_tx(BranchId::Sapling)) {
        check_roundtrip(tx)?;
    }
}

proptest! {
    #[test]
    #[cfg(all(feature = "expensive-tests", not(feature = "no-expensive-tests")))]
    fn tx_serialization_roundtrip_blossom(tx in arb_tx(BranchId::Blossom)) {
        check_roundtrip(tx)?;
    }
}

proptest! {
    #[test]
    #[cfg(all(feature = "expensive-tests", not(feature = "no-expensive-tests")))]
    fn tx_serialization_roundtrip_heartwood(tx in arb_tx(BranchId::Heartwood)) {
        check_roundtrip(tx)?;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
    fn tx_serialization_roundtrip_canopy(tx in arb_tx(BranchId::Canopy)) {
        check_roundtrip(tx)?;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
    fn tx_serialization_roundtrip_nu5(tx in arb_tx(BranchId::Nu5)) {
        check_roundtrip(tx)?;
    }
}

#[cfg(test)]
proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
    fn tx_serialization_roundtrip_nu6_3(tx in arb_tx(BranchId::Nu6_3)) {
        check_roundtrip(tx)?;
    }
}

#[cfg(test)]
proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]
    #[test]
    fn tx_serialization_roundtrip_nu7(tx in arb_tx(BranchId::Nu7)) {
        check_roundtrip(tx)?;
    }
}

#[test]
fn zip_0143() {
    for tv in self::data::zip_0143::make_test_vectors() {
        let tx = Transaction::read(&tv.tx[..], tv.consensus_branch_id).unwrap();
        let signable_input = match tv.transparent_input {
            Some(n) => SignableInput::Transparent(
                ::transparent::sighash::SignableInput::from_parts(
                    tx.transparent_bundle().unwrap(),
                    SighashType::parse(tv.hash_type as u8).unwrap(),
                    n as usize,
                    &tv.script_code,
                    &tv.script_code,
                    Zatoshis::from_nonnegative_i64(tv.amount).unwrap(),
                )
                .unwrap(),
            ),
            _ => SignableInput::Shielded,
        };

        assert_eq!(
            v4_signature_hash(tx.deref(), &signable_input).as_ref(),
            tv.sighash
        );

        let precomputed =
            PrecomputedSighashData::new(with_test_transparent_auth(tx.deref(), vec![], vec![]));
        assert_eq!(
            precomputed.signature_hash(&signable_input).as_ref(),
            &tv.sighash
        );
        check_v4_precomputed_matches_legacy(&precomputed);
    }
}

#[test]
fn zip_0243() {
    for tv in self::data::zip_0243::make_test_vectors() {
        let tx = Transaction::read(&tv.tx[..], tv.consensus_branch_id).unwrap();
        let signable_input = match tv.transparent_input {
            Some(n) => SignableInput::Transparent(
                ::transparent::sighash::SignableInput::from_parts(
                    tx.transparent_bundle().unwrap(),
                    SighashType::parse(tv.hash_type as u8).unwrap(),
                    n as usize,
                    &tv.script_code,
                    &tv.script_code,
                    Zatoshis::from_nonnegative_i64(tv.amount).unwrap(),
                )
                .unwrap(),
            ),
            _ => SignableInput::Shielded,
        };

        assert_eq!(
            v4_signature_hash(tx.deref(), &signable_input).as_ref(),
            tv.sighash
        );

        let precomputed =
            PrecomputedSighashData::new(with_test_transparent_auth(tx.deref(), vec![], vec![]));
        assert_eq!(
            precomputed.signature_hash(&signable_input).as_ref(),
            &tv.sighash
        );
        check_v4_precomputed_matches_legacy(&precomputed);

        // The signature hash of each input takes the digests of the transparent inputs and
        // outputs, JoinSplits and Sapling spends and outputs from the precomputed digests,
        // instead of hashing the transaction again.
        let digests = zip143_digests(tx.deref());
        assert_eq!(
            v4_signature_hash_with_digests(tx.deref(), &signable_input, &digests).as_ref(),
            tv.sighash
        );
        let mut replaced = digests.clone();
        let other = blake2b_simd::Params::new().hash_length(32).hash(b"other");
        replaced.prevouts = other;
        replaced.sequence = other;
        replaced.outputs = other;
        replaced.joinsplits = replaced.joinsplits.map(|_| other);
        replaced.sapling_spends = replaced.sapling_spends.map(|_| other);
        replaced.sapling_outputs = replaced.sapling_outputs.map(|_| other);
        let hash_type = signable_input.hash_type();
        let uses_shared_digests = hash_type & ::transparent::sighash::SIGHASH_ANYONECANPAY == 0
            || !matches!(
                hash_type & ::transparent::sighash::SIGHASH_MASK,
                ::transparent::sighash::SIGHASH_NONE | ::transparent::sighash::SIGHASH_SINGLE
            )
            || digests.joinsplits.is_some()
            || digests.sapling_spends.is_some()
            || digests.sapling_outputs.is_some();
        assert_eq!(
            v4_signature_hash_with_digests(tx.deref(), &signable_input, &replaced).as_ref()
                == tv.sighash,
            !uses_shared_digests
        );
    }
}

/// Checks that the precomputed signature hash of every transparent input under every
/// canonical hash type, and of the shielded input, of a version 4 or earlier transaction
/// matches the signature hash computed without precomputation.
#[cfg(test)]
fn check_v4_precomputed_matches_legacy(precomputed: &PrecomputedSighashData<TestUnauthorized>) {
    let tx = precomputed.tx();
    let script_code = Script(script::Code(vec![0x51]));
    let check = |signable_input: &SignableInput<'_>| {
        assert_eq!(
            precomputed.signature_hash(signable_input).as_ref(),
            v4_signature_hash(tx, signable_input).as_bytes()
        );
    };
    check(&SignableInput::Shielded);
    if let Some(bundle) = tx.transparent_bundle() {
        for index in 0..bundle.vin.len() {
            for hash_type in ALL_HASH_TYPES {
                check(&SignableInput::Transparent(
                    ::transparent::sighash::SignableInput::from_parts(
                        bundle,
                        hash_type,
                        index,
                        &script_code,
                        &script_code,
                        Zatoshis::const_from_u64(1),
                    )
                    .unwrap(),
                ));
            }
        }
    }
}

/// The six canonical transparent signature hash types.
#[cfg(test)]
const ALL_HASH_TYPES: [SighashType; 6] = [
    SighashType::ALL,
    SighashType::NONE,
    SighashType::SINGLE,
    SighashType::ALL_ANYONECANPAY,
    SighashType::NONE_ANYONECANPAY,
    SighashType::SINGLE_ANYONECANPAY,
];

#[cfg(test)]
#[derive(Debug)]
struct TestTransparentAuth {
    input_amounts: Vec<Zatoshis>,
    input_scriptpubkeys: Vec<Script>,
    /// The number of calls to `input_amounts` and `input_scriptpubkeys`.
    reads: Cell<usize>,
}

#[cfg(test)]
impl TestTransparentAuth {
    fn new(input_amounts: Vec<Zatoshis>, input_scriptpubkeys: Vec<Script>) -> Self {
        TestTransparentAuth {
            input_amounts,
            input_scriptpubkeys,
            reads: Cell::new(0),
        }
    }
}

/// Returns a copy of `txdata` whose transparent inputs spend outputs with the given
/// `input_amounts` and `input_scriptpubkeys`.
#[cfg(test)]
fn with_test_transparent_auth(
    txdata: &TransactionData<Authorized>,
    input_amounts: Vec<Zatoshis>,
    input_scriptpubkeys: Vec<Script>,
) -> TransactionData<TestUnauthorized> {
    let test_bundle = txdata
        .transparent_bundle
        .as_ref()
        .map(|b| transparent::Bundle {
            // we have to do this map/clone to make the types line up, since the
            // Authorization::ScriptSig type is bound to transparent::Authorized, and we need
            // it to be bound to TestTransparentAuth.
            vin: b
                .vin
                .iter()
                .map(|vin| {
                    TxIn::from_parts(
                        vin.prevout().clone(),
                        vin.script_sig().clone(),
                        vin.sequence(),
                    )
                })
                .collect(),
            vout: b.vout.clone(),
            authorization: TestTransparentAuth::new(input_amounts, input_scriptpubkeys),
        });

    if txdata.version() == TxVersion::V6 {
        TransactionData::from_parts_v6(
            txdata.consensus_branch_id(),
            txdata.lock_time(),
            txdata.expiry_height(),
            test_bundle,
            txdata.sapling_bundle().cloned(),
            txdata.orchard_bundle().cloned(),
            txdata.ironwood_bundle().cloned(),
        )
    } else {
        TransactionData::from_parts(
            txdata.version(),
            txdata.consensus_branch_id(),
            txdata.lock_time(),
            txdata.expiry_height(),
            test_bundle,
            txdata.sprout_bundle().cloned(),
            txdata.sapling_bundle().cloned(),
            txdata.orchard_bundle().cloned(),
        )
    }
}

#[cfg(test)]
impl transparent::Authorization for TestTransparentAuth {
    type ScriptSig = Script;
}

#[cfg(test)]
impl TransparentAuthorizingContext for TestTransparentAuth {
    fn input_amounts(&self) -> Vec<Zatoshis> {
        self.reads.set(self.reads.get() + 1);
        self.input_amounts.clone()
    }

    fn input_scriptpubkeys(&self) -> Vec<Script> {
        self.reads.set(self.reads.get() + 1);
        self.input_scriptpubkeys.clone()
    }
}

#[cfg(test)]
struct TestUnauthorized;

#[cfg(test)]
impl Authorization for TestUnauthorized {
    type TransparentAuth = TestTransparentAuth;
    type SaplingAuth = sapling::bundle::Authorized;
    type OrchardAuth = orchard::bundle::Authorized;
}

#[test]
fn zip_0244() {
    fn to_test_txdata(
        tv: &self::data::zip_0244::TestVector,
    ) -> (TransactionData<TestUnauthorized>, TxDigests<Blake2bHash>) {
        let tx = Transaction::read(&tv.tx[..], BranchId::Nu5).unwrap();

        assert_eq!(tx.txid.as_ref(), &tv.txid);
        assert_eq!(tx.auth_commitment().as_ref(), &tv.auth_digest);

        let txdata = tx.deref();

        let input_amounts = tv
            .amounts
            .iter()
            .map(|amount| Zatoshis::from_nonnegative_i64(*amount).unwrap())
            .collect();
        let input_scriptpubkeys = tv
            .script_pubkeys
            .iter()
            .cloned()
            .map(script::Code)
            .map(Script)
            .collect();

        let test_bundle = txdata
            .transparent_bundle
            .as_ref()
            .map(|b| transparent::Bundle {
                // we have to do this map/clone to make the types line up, since the
                // Authorization::ScriptSig type is bound to transparent::Authorized, and we need
                // it to be bound to TestTransparentAuth.
                vin: b
                    .vin
                    .iter()
                    .map(|vin| {
                        TxIn::from_parts(
                            vin.prevout().clone(),
                            vin.script_sig().clone(),
                            vin.sequence(),
                        )
                    })
                    .collect(),
                vout: b.vout.clone(),
                authorization: TestTransparentAuth::new(input_amounts, input_scriptpubkeys),
            });

        let tdata = TransactionData::from_parts(
            txdata.version(),
            txdata.consensus_branch_id(),
            txdata.lock_time(),
            txdata.expiry_height(),
            test_bundle,
            txdata.sprout_bundle().cloned(),
            txdata.sapling_bundle().cloned(),
            txdata.orchard_bundle().cloned(),
        );
        (tdata, txdata.digest(TxIdDigester))
    }

    for tv in self::data::zip_0244::make_test_vectors() {
        let (txdata, txid_parts) = to_test_txdata(&tv);
        let precomputed = PrecomputedSighashData::new(txdata);
        let txdata = precomputed.tx();

        // Computes the signature hash both without and with precomputation, and checks
        // that the results agree.
        let check_sighash = |signable_input: &SignableInput<'_>| {
            let sighash = v5_signature_hash(txdata, signable_input, &txid_parts);
            assert_eq!(
                precomputed.signature_hash(signable_input).as_ref(),
                sighash.as_bytes()
            );
            assert_eq!(
                signature_hash(txdata, signable_input, &txid_parts).as_ref(),
                sighash.as_bytes()
            );
            sighash
        };

        if let Some(index) = tv.transparent_input {
            // nIn is a u32, but to actually use it we need a usize.
            let index = index as usize;
            let bundle = txdata.transparent_bundle().unwrap();
            let value = bundle.authorization.input_amounts[index];
            let script_pubkey = &bundle.authorization.input_scriptpubkeys[index];
            let signable_input = |hash_type| {
                SignableInput::Transparent(
                    ::transparent::sighash::SignableInput::from_parts(
                        bundle,
                        hash_type,
                        index,
                        script_pubkey,
                        script_pubkey,
                        value,
                    )
                    .unwrap(),
                )
            };

            assert_eq!(
                check_sighash(&signable_input(SighashType::ALL)).as_ref(),
                &tv.sighash_all.unwrap()
            );

            assert_eq!(
                check_sighash(&signable_input(SighashType::NONE)).as_ref(),
                &tv.sighash_none.unwrap()
            );

            if index < bundle.vout.len() {
                assert_eq!(
                    check_sighash(&signable_input(SighashType::SINGLE)).as_ref(),
                    &tv.sighash_single.unwrap()
                );
            } else {
                assert_eq!(tv.sighash_single, None);
            }

            assert_eq!(
                check_sighash(&signable_input(SighashType::ALL_ANYONECANPAY)).as_ref(),
                &tv.sighash_all_anyone.unwrap()
            );

            assert_eq!(
                check_sighash(&signable_input(SighashType::NONE_ANYONECANPAY)).as_ref(),
                &tv.sighash_none_anyone.unwrap()
            );

            if index < bundle.vout.len() {
                assert_eq!(
                    check_sighash(&signable_input(SighashType::SINGLE_ANYONECANPAY)).as_ref(),
                    &tv.sighash_single_anyone.unwrap()
                );
            } else {
                assert_eq!(tv.sighash_single_anyone, None);
            }
        };

        assert_eq!(
            check_sighash(&SignableInput::Shielded).as_ref(),
            tv.sighash_shielded
        );

        // Computing the signature hashes of every input under every hash type, including
        // `SIGHASH_SINGLE` for inputs without a corresponding output, and of the shielded
        // input, reads the input amounts and `scriptPubKey`s once each, when the digests
        // are precomputed. Coinbase transactions and transactions without transparent
        // inputs never read them.
        let precomputed = PrecomputedSighashData::new(to_test_txdata(&tv).0);
        let reads_on_precompute = precomputed
            .tx()
            .transparent_bundle()
            .map_or(0, |b| b.authorization.reads.get());
        precomputed.signature_hash(&SignableInput::Shielded);
        if let Some(bundle) = precomputed.tx().transparent_bundle() {
            let has_inputs = !bundle.is_coinbase() && !bundle.vin.is_empty();
            assert_eq!(reads_on_precompute, if has_inputs { 2 } else { 0 });
            assert_eq!(bundle.authorization.reads.get(), reads_on_precompute);
            if has_inputs {
                for index in 0..bundle.vin.len() {
                    let script_pubkey = &bundle.authorization.input_scriptpubkeys[index];
                    for hash_type in ALL_HASH_TYPES {
                        let signable_input = SignableInput::Transparent(
                            ::transparent::sighash::SignableInput::from_parts(
                                bundle,
                                hash_type,
                                index,
                                script_pubkey,
                                script_pubkey,
                                bundle.authorization.input_amounts[index],
                            )
                            .unwrap(),
                        );
                        let reads = bundle.authorization.reads.get();
                        let legacy =
                            v5_signature_hash(precomputed.tx(), &signable_input, &txid_parts);
                        assert_eq!(
                            precomputed.signature_hash(&signable_input).as_ref(),
                            legacy.as_bytes()
                        );
                        // Without precomputation, each signature hash that commits to the
                        // input amounts and `scriptPubKey`s reads them again.
                        let legacy_reads = if hash_type.encode()
                            & ::transparent::sighash::SIGHASH_ANYONECANPAY
                            == 0
                        {
                            2
                        } else {
                            0
                        };
                        assert_eq!(bundle.authorization.reads.get(), reads + legacy_reads);
                    }
                }
            }
        }
    }
}

#[test]
fn v6_signature_hashes_match_independent_values() {
    // The synthetic version 6 transaction from
    // `v6_encoding_hashes_and_fee_are_independent_of_nu7_cfg`, whose one input spends a
    // 65000 zatoshi output with `scriptPubKey` `OP_TRUE`. The expected signature hashes
    // were computed independently with Python hashlib.blake2b, following the ZIP 244
    // signature digest with the version 6 empty Sapling, Orchard and Ironwood digests.
    let bytes = hex::decode("0600008098b684d85b16a53701000000020000000100000000000000000000000000000000000000000000000000000000000000000000000000ffffffff0150c3000000000000015100000000").unwrap();
    let tx = Transaction::read(&bytes[..], BranchId::Nu6_3).unwrap();
    let script_pubkey = Script(script::Code(vec![0x51]));
    let value = Zatoshis::const_from_u64(65_000);
    let txdata = with_test_transparent_auth(tx.deref(), vec![value], vec![script_pubkey.clone()]);
    let txid_parts = txdata.digest(TxIdDigester);
    let precomputed = PrecomputedSighashData::new_zip244(txdata).unwrap();
    let txdata = precomputed.tx();
    let bundle = txdata.transparent_bundle().unwrap();

    // The input amounts and `scriptPubKey`s were read once each, when precomputing.
    assert_eq!(bundle.authorization.reads.get(), 2);

    let check = |signable_input: &SignableInput<'_>, expected: &str| {
        let reads = bundle.authorization.reads.get();
        assert_eq!(
            hex::encode(precomputed.signature_hash(signable_input).as_ref()),
            expected
        );
        // Signing with the precomputed digests does not read them again.
        assert_eq!(bundle.authorization.reads.get(), reads);
        assert_eq!(
            hex::encode(v6_signature_hash(txdata, signable_input, &txid_parts).as_bytes()),
            expected
        );
        assert_eq!(
            hex::encode(signature_hash(txdata, signable_input, &txid_parts).as_ref()),
            expected
        );
    };

    check(
        &SignableInput::Shielded,
        "e578a96e09df5cccb704c5e31a6c2d3036c6e643ff5e936ff357e022fe5fe125",
    );
    for (hash_type, expected) in ALL_HASH_TYPES.into_iter().zip([
        "a9ea94cb98c86b2ea59aaffd150685e7393da151d02bd269cb16937ccc520c7a",
        "460e26bfb4510a8c4c3eafc545ae00d45a0071671847fe5526b01a49075d6ecd",
        "9438babdf52d52af0115bdfd6d909b18ae52fdd392371f5aa1b2321baf8f00f9",
        "9088337ed7401d7c6587c9662a5399737160ca183ac6150749c94e7ca32f3401",
        "5fbd6a2157fad3a1ce0161195261d0d9b19e87848cf55de20b9f8605c5369748",
        "aa2baf9945baaf63de5cb20c4f9fa279e416a886606c23b04eb430c7c6afb6ab",
    ]) {
        check(
            &SignableInput::Transparent(
                ::transparent::sighash::SignableInput::from_parts(
                    bundle,
                    hash_type,
                    0,
                    &script_pubkey,
                    &script_pubkey,
                    value,
                )
                .unwrap(),
            ),
            expected,
        );
    }
}

#[test]
fn precomputed_sighash_zip244_constructor_rejects_v4_and_accepts_v5() {
    for tv in self::data::zip_0243::make_test_vectors() {
        let tx = Transaction::read(&tv.tx[..], tv.consensus_branch_id).unwrap();
        let txdata = with_test_transparent_auth(tx.deref(), vec![], vec![]);
        match PrecomputedSighashData::new_zip244(txdata) {
            Err(Zip244Error::NotZip244(txdata)) => {
                // The transaction is returned unchanged.
                assert_eq!(txdata.version(), tx.version());
                assert_eq!(
                    txdata.transparent_bundle().map(|b| b.vin.len()),
                    tx.transparent_bundle().map(|b| b.vin.len())
                );
                assert_eq!(
                    zip143_digests(&*txdata).prevouts,
                    zip143_digests(tx.deref()).prevouts
                );
            }
            Ok(_) => panic!("a version 4 transaction was accepted"),
        }
    }

    for tv in self::data::zip_0244::make_test_vectors() {
        let tx = Transaction::read(&tv.tx[..], BranchId::Nu5).unwrap();
        let amounts = tv
            .amounts
            .iter()
            .map(|amount| Zatoshis::from_nonnegative_i64(*amount).unwrap())
            .collect::<Vec<_>>();
        let scripts = tv
            .script_pubkeys
            .iter()
            .cloned()
            .map(|s| Script(script::Code(s)))
            .collect::<Vec<_>>();
        let zip244 = PrecomputedSighashData::new_zip244(with_test_transparent_auth(
            tx.deref(),
            amounts.clone(),
            scripts.clone(),
        ))
        .unwrap();
        let general =
            PrecomputedSighashData::new(with_test_transparent_auth(tx.deref(), amounts, scripts));
        assert_eq!(
            zip244.signature_hash(&SignableInput::Shielded).as_ref(),
            general.signature_hash(&SignableInput::Shielded).as_ref()
        );
        assert_eq!(
            zip244.signature_hash(&SignableInput::Shielded).as_ref(),
            &tv.sighash_shielded
        );
    }
}

#[test]
fn precomputed_sighash_follows_the_transaction_it_was_computed_for() {
    let mut checked = false;
    for tv in self::data::zip_0244::make_test_vectors() {
        let Some(index) = tv.transparent_input else {
            continue;
        };
        let index = index as usize;
        let tx = Transaction::read(&tv.tx[..], BranchId::Nu5).unwrap();
        let amounts = tv
            .amounts
            .iter()
            .map(|amount| Zatoshis::from_nonnegative_i64(*amount).unwrap())
            .collect::<Vec<_>>();
        let scripts = tv
            .script_pubkeys
            .iter()
            .cloned()
            .map(|s| Script(script::Code(s)))
            .collect::<Vec<_>>();

        // The same transaction, except that the input being signed spends one more zatoshi,
        // and another input spends one more zatoshi too if there is one.
        let mut changed_amounts = amounts.clone();
        for amount in changed_amounts.iter_mut() {
            *amount = (*amount + Zatoshis::const_from_u64(1)).unwrap();
        }

        let original = PrecomputedSighashData::new(with_test_transparent_auth(
            tx.deref(),
            amounts.clone(),
            scripts.clone(),
        ));
        let changed = PrecomputedSighashData::new(with_test_transparent_auth(
            tx.deref(),
            changed_amounts.clone(),
            scripts.clone(),
        ));

        let sighash = |precomputed: &PrecomputedSighashData<TestUnauthorized>,
                       amounts: &[Zatoshis],
                       hash_type| {
            let bundle = precomputed.tx().transparent_bundle().unwrap();
            let signable_input = SignableInput::Transparent(
                ::transparent::sighash::SignableInput::from_parts(
                    bundle,
                    hash_type,
                    index,
                    &scripts[index],
                    &scripts[index],
                    amounts[index],
                )
                .unwrap(),
            );
            let txid_parts = precomputed.tx().digest(TxIdDigester);
            let legacy = v5_signature_hash(precomputed.tx(), &signable_input, &txid_parts);
            let cached = precomputed.signature_hash(&signable_input);
            assert_eq!(cached.as_ref(), legacy.as_bytes());
            *cached.as_ref()
        };

        // The original digests still give the known signature hash after the changed
        // transaction's digests are computed, and the changed transaction's signature hash
        // commits to its own amounts.
        assert_eq!(
            sighash(&original, &amounts, SighashType::ALL),
            tv.sighash_all.unwrap()
        );
        assert_ne!(
            sighash(&changed, &changed_amounts, SighashType::ALL),
            tv.sighash_all.unwrap()
        );
        // With `SIGHASH_ANYONECANPAY`, only the amount of the input being signed changes
        // the signature hash, and it changed here.
        assert_ne!(
            sighash(&changed, &changed_amounts, SighashType::ALL_ANYONECANPAY),
            tv.sighash_all_anyone.unwrap()
        );

        // Taking the transaction back and computing its digests again gives the same
        // signature hashes.
        let recomputed = PrecomputedSighashData::new(original.into_tx());
        assert_eq!(
            sighash(&recomputed, &amounts, SighashType::ALL),
            tv.sighash_all.unwrap()
        );
        checked = true;
    }
    assert!(checked);
}
