//! Tests of building v7 transactions.

use alloc::vec;
use alloc::vec::Vec;
use core::convert::Infallible;

use assert_matches::assert_matches;
use rand::rng as thread_rng;

use ::transparent::address::TransparentAddress;
use zcash_protocol::{
    consensus::{BlockHeight, BranchId},
    local_consensus::LocalNetwork,
    value::{ZatBalance, Zatoshis},
};

use crate::transaction::{
    Transaction, TxVersion,
    builder::{BuildConfig, Builder, BundlePadding, Error, V7CoinbaseConfig},
    v7::{CoinbaseError, ValueDeltas},
};

/// The height at which [`network`] activates NU7.1.
const NU7_1: u32 = 12;

/// A local network that activates every upgrade by height 11, and NU7.1 at [`NU7_1`].
fn network() -> LocalNetwork {
    let at = |h: u32| Some(BlockHeight::from_u32(h));
    LocalNetwork {
        overwinter: at(1),
        sapling: at(2),
        blossom: at(3),
        heartwood: at(4),
        canopy: at(5),
        nu5: at(6),
        nu6: at(7),
        nu6_1: at(8),
        nu6_2: at(9),
        nu6_3: at(10),
        nu7: at(11),
        nu7_1: at(NU7_1),
    }
}

fn standard(ironwood_anchor: Option<orchard::Anchor>) -> BuildConfig {
    BuildConfig::Standard {
        sapling_anchor: None,
        orchard_anchor: None,
        ironwood_anchor,
        orchard_padding: BundlePadding::DEFAULT,
        ironwood_padding: BundlePadding::DEFAULT,
    }
}

/// Writes and reads back `tx`. Reading checks the ZIP 248 bundle-local rules again, so
/// every built transaction that passes through here satisfies them.
fn round_trip(tx: &Transaction) -> Transaction {
    let mut bytes = Vec::new();
    tx.write(&mut bytes).unwrap();
    let parsed = Transaction::read(&bytes[..], BranchId::Nu7_1).unwrap();
    assert_eq!(parsed.txid(), tx.txid());
    parsed
}

/// The sum of a v7 transaction's value pool deltas, which consensus requires to be zero.
fn delta_sum(tx: &Transaction) -> i64 {
    tx.value_pool_deltas()
        .unwrap()
        .iter()
        .map(|d| d.value.get())
        .sum()
}

#[test]
fn builder_makes_v7_only_on_request() {
    // Without a request, the builder keeps the oldest format NU7.1 accepts.
    let mut legacy = Builder::new(
        network(),
        NU7_1.into(),
        BuildConfig::Coinbase { miner_data: None },
    );
    legacy
        .add_transparent_output(
            &TransparentAddress::PublicKeyHash([7; 20]),
            Zatoshis::const_from_u64(1),
        )
        .unwrap();
    assert_eq!(build_coinbase(legacy).unwrap().version(), TxVersion::V6);

    let mut builder = Builder::new(network(), NU7_1.into(), standard(None));
    builder
        .propose_version::<Infallible>(TxVersion::V7)
        .unwrap();

    // Before NU7.1, v7 is not valid.
    let mut early = Builder::new(network(), (NU7_1 - 1).into(), standard(None));
    assert_matches!(
        early.propose_version::<Infallible>(TxVersion::V7),
        Err(Error::TargetIncompatible(
            BranchId::Nu7,
            TxVersion::V7,
            None
        ))
    );
}

/// Consensus rejects a v7 transaction that expires above ZIP 203's limit, so the builder
/// refuses to make one, whether the expiry is set before or after v7 is proposed.
#[test]
fn v7_builder_rejects_an_expiry_height_above_the_limit() {
    let limit = BlockHeight::from_u32(499_999_999);
    let too_high = limit + 1;

    let mut early =
        Builder::new(network(), NU7_1.into(), standard(None)).with_expiry_height(too_high);
    assert_matches!(
        early.propose_version::<Infallible>(TxVersion::V7),
        Err(Error::InvalidExpiryHeight { expiry_height }) if expiry_height == too_high
    );

    let mut builder = Builder::new(network(), NU7_1.into(), standard(None));
    builder
        .propose_version::<Infallible>(TxVersion::V7)
        .unwrap();
    let signing_set = ::transparent::builder::TransparentSigningSet::new();
    assert_matches!(
        builder
            .with_expiry_height(too_high)
            .mock_build(&signing_set, &[], &[], thread_rng()),
        Err(Error::InvalidExpiryHeight { expiry_height }) if expiry_height == too_high
    );

    let mut at_limit =
        Builder::new(network(), NU7_1.into(), standard(None)).with_expiry_height(limit);
    at_limit
        .propose_version::<Infallible>(TxVersion::V7)
        .unwrap();
}

#[cfg(feature = "transparent-inputs")]
#[test]
fn transparent_v7_transaction_balances_and_signs() {
    use ::transparent::{
        builder::TransparentSigningSet,
        bundle::{OutPoint, TxOut},
        keys::{AccountPrivKey, NonHardenedChildIndex},
        sighash::{SighashType, SignableInput as TransparentSignableInput},
    };
    use zip32::AccountId;

    use super::transaction::{SpentOutputs, with_spent_outputs};
    use crate::transaction::{
        TxIdDigester,
        sighash::{SignableInput, signature_hash},
    };

    let mut builder = Builder::new(network(), NU7_1.into(), standard(None));
    builder
        .propose_version::<Infallible>(TxVersion::V7)
        .unwrap();

    let mut signing_set = TransparentSigningSet::new();
    let tsk = AccountPrivKey::from_seed(&network(), &[0u8; 32], AccountId::ZERO).unwrap();
    let pubkey = signing_set.add_key(
        tsk.derive_external_secret_key(NonHardenedChildIndex::ZERO)
            .unwrap(),
    );
    let prev_coin = TxOut::new(
        Zatoshis::const_from_u64(50_000),
        TransparentAddress::from_pubkey(&pubkey).script().into(),
    );
    builder
        .add_transparent_p2pkh_input(pubkey, OutPoint::fake(), prev_coin.clone())
        .unwrap();
    builder
        .add_transparent_output(
            &TransparentAddress::PublicKeyHash([0; 20]),
            Zatoshis::const_from_u64(40_000),
        )
        .unwrap();

    let tx = builder
        .mock_build(&signing_set, &[], &[], thread_rng())
        .unwrap()
        .transaction()
        .clone();
    let tx = round_trip(&tx);
    assert_eq!(tx.version(), TxVersion::V7);
    let fields = tx.v7_fields().unwrap();
    assert_eq!(fields.coinbase_bundle, None);
    assert_eq!(
        fields.value_deltas.transparent,
        ZatBalance::const_from_i64(10_000)
    );
    assert_eq!(fields.value_deltas.fee, ZatBalance::const_from_i64(-10_000));
    assert_eq!(delta_sum(&tx), 0);

    // The P2PKH signature verifies against the v7 digest of its input, which commits to
    // the spent output, and its hash type is SIGHASH_ALL.
    let verifying = with_spent_outputs(
        &tx,
        SpentOutputs {
            reads: Default::default(),
            amounts: vec![prev_coin.value()],
            script_pubkeys: vec![prev_coin.script_pubkey().clone()],
        },
    );
    let txid_parts = verifying.digest(TxIdDigester);
    let bundle = verifying.transparent_bundle().unwrap();
    let sighash = signature_hash(
        &verifying,
        &SignableInput::Transparent(
            TransparentSignableInput::from_parts(
                bundle,
                SighashType::ALL,
                0,
                prev_coin.script_pubkey(),
                prev_coin.script_pubkey(),
                prev_coin.value(),
            )
            .unwrap(),
        ),
        &txid_parts,
    )
    .unwrap();
    let script_sig = &bundle.vin[0].script_sig().0.0;
    let sig_len = usize::from(script_sig[0]);
    let (der, hash_type) = script_sig[1..=sig_len].split_at(sig_len - 1);
    assert_eq!(hash_type, [SighashType::ALL.encode()]);
    let signature = secp256k1::ecdsa::Signature::from_der(der).unwrap();
    let message = secp256k1::Message::from_digest(*sighash.as_ref());
    signature.verify(message, &pubkey).unwrap();

    // The input passes the script interpreter under the v7 rules, which require
    // SIGHASH_ALL, with the v7 digest of whatever hash type a signature states.
    let checker = zcash_script::interpreter::CallbackTransactionSignatureChecker {
        sighash: &|script_code, hash_type| {
            let script_code = ::transparent::address::Script(script_code.clone());
            let hash_type = u8::try_from(hash_type.raw_bits()).ok()?;
            let input = TransparentSignableInput::from_parts(
                bundle,
                SighashType::parse(hash_type)?,
                0,
                &script_code,
                prev_coin.script_pubkey(),
                prev_coin.value(),
            )
            .ok()?;
            signature_hash(&verifying, &SignableInput::Transparent(input), &txid_parts)
                .ok()
                .map(|sighash| *sighash.as_ref())
        },
        lock_time: tx.lock_time().into(),
        is_final: bundle.vin[0].sequence() == u32::MAX,
    };
    let spend = |script_sig: Vec<u8>| {
        zcash_script::script::Raw::from_raw_parts(script_sig, prev_coin.script_pubkey().0.0.clone())
            .eval(
                zcash_script::interpreter::Flags::P2SH
                    | zcash_script::interpreter::Flags::CHECKLOCKTIMEVERIFY
                    | zcash_script::interpreter::Flags::SigHashAllOnly,
                &checker,
            )
            .map_err(|(_, e)| e)
    };
    assert_eq!(spend(script_sig.clone()), Ok(true));

    // The same signature with another hash type byte fails the SIGHASH_ALL rule.
    let mut other_hash_type = script_sig.clone();
    other_hash_type[sig_len] = SighashType::ALL_ANYONECANPAY.encode();
    assert_matches!(
        spend(other_hash_type),
        Err(zcash_script::script::Error::Interpreter(
            _,
            zcash_script::interpreter::Error::SigHashNotAll
        ))
    );
}

/// A shielding transaction's Ironwood bundle, with real proofs, verifies only against the
/// per-signature v7 digests.
#[cfg(feature = "transparent-inputs")]
#[test]
fn shielding_v7_transaction_signs_each_signature_over_its_own_digest() {
    use ::transparent::{
        builder::TransparentSigningSet,
        bundle::{OutPoint, TxOut},
        keys::{AccountPrivKey, NonHardenedChildIndex},
    };
    use zip32::AccountId;

    use super::transaction::{SpentOutputs, with_spent_outputs};
    use crate::transaction::{
        components::orchard, sighash::V7SignatureHashes, v7::ShieldedBundleType,
    };
    use zcash_protocol::memo::MemoBytes;

    let mut builder = Builder::new(
        network(),
        NU7_1.into(),
        standard(Some(::orchard::Anchor::empty_tree())),
    );
    builder
        .propose_version::<Infallible>(TxVersion::V7)
        .unwrap();

    let mut signing_set = TransparentSigningSet::new();
    let tsk = AccountPrivKey::from_seed(&network(), &[0u8; 32], AccountId::ZERO).unwrap();
    let pubkey = signing_set.add_key(
        tsk.derive_external_secret_key(NonHardenedChildIndex::ZERO)
            .unwrap(),
    );
    let prev_coin = TxOut::new(
        Zatoshis::const_from_u64(100_000),
        TransparentAddress::from_pubkey(&pubkey).script().into(),
    );
    builder
        .add_transparent_p2pkh_input(pubkey, OutPoint::fake(), prev_coin.clone())
        .unwrap();
    let recipient = ::orchard::keys::FullViewingKey::from(
        &::orchard::keys::SpendingKey::from_bytes([0; 32]).unwrap(),
    )
    .address_at(0u32, ::orchard::keys::Scope::External);
    builder
        .add_ironwood_output::<Infallible>(
            None,
            recipient,
            Zatoshis::const_from_u64(85_000),
            MemoBytes::empty(),
        )
        .unwrap();

    let tx = builder
        .mock_build(&signing_set, &[], &[], thread_rng())
        .unwrap()
        .transaction()
        .clone();
    let tx = round_trip(&tx);
    assert_eq!(delta_sum(&tx), 0);
    let ironwood = tx.ironwood_bundle().unwrap();
    assert!(ironwood.actions().len() >= 2, "padding adds a dummy spend");

    let verifying = with_spent_outputs(
        &tx,
        SpentOutputs {
            reads: Default::default(),
            amounts: vec![prev_coin.value()],
            script_pubkeys: vec![prev_coin.script_pubkey().clone()],
        },
    );
    let sighashes = V7SignatureHashes::new(&verifying)
        .unwrap()
        .shielded_sighashes(ShieldedBundleType::Ironwood)
        .unwrap();
    let circuit =
        orchard::bundle_version_for_branch(BranchId::Nu7_1, ::orchard::ValuePool::Ironwood)
            .unwrap()
            .circuit_version();
    let vk = ::orchard::circuit::VerifyingKey::build(circuit);
    let validates = |sighashes: &dyn Fn(&mut ::orchard::bundle::BatchValidator<'_>)| {
        let mut validator = ::orchard::bundle::BatchValidator::new(&vk);
        sighashes(&mut validator);
        validator.validate(thread_rng())
    };
    assert!(validates(&|v| v
        .add_bundle(ironwood, sighashes.clone())
        .unwrap()));
    assert!(!validates(&|v| v.add_bundle(ironwood, [0; 32]).unwrap()));
}

fn v7_coinbase(fees: u64, nsm: u64) -> V7CoinbaseConfig {
    let mut config = V7CoinbaseConfig::new(
        Zatoshis::const_from_u64(312_500_000),
        Zatoshis::const_from_u64(37_500_000),
        Zatoshis::const_from_u64(fees),
        Zatoshis::const_from_u64(nsm),
    );
    config.coinbase_data = b"zakura".to_vec();
    config
}

/// The value a v7 coinbase transaction's outputs must pay for [`v7_coinbase`].
fn miner_reward(fees: u64, nsm: u64) -> u64 {
    312_500_000 - 37_500_000 + fees - nsm
}

fn coinbase_builder(config: V7CoinbaseConfig, paid: u64) -> Builder<LocalNetwork, ()> {
    let mut builder = Builder::new(network(), NU7_1.into(), BuildConfig::V7Coinbase(config));
    builder
        .add_transparent_output(
            &TransparentAddress::PublicKeyHash([7; 20]),
            Zatoshis::from_u64(paid).unwrap(),
        )
        .unwrap();
    builder
}

fn build_coinbase(builder: Builder<LocalNetwork, ()>) -> Result<Transaction, Error<Infallible>> {
    builder
        .build_coinbase(
            thread_rng(),
            &::sapling::prover::mock::MockSpendProver,
            &::sapling::prover::mock::MockOutputProver,
        )
        .map(|res| res.transaction().clone())
}

#[test]
fn v7_coinbase_states_its_block_and_balances() {
    let (fees, nsm) = (10_000, 6_000);
    let tx = build_coinbase(coinbase_builder(
        v7_coinbase(fees, nsm),
        miner_reward(fees, nsm),
    ))
    .unwrap();
    let tx = round_trip(&tx);

    assert_eq!(tx.version(), TxVersion::V7);
    assert!(tx.is_coinbase());
    assert_eq!(tx.expiry_height(), BlockHeight::from_u32(NU7_1));
    assert!(tx.transparent_bundle().unwrap().vin.is_empty());
    let coinbase = tx.coinbase_bundle().unwrap();
    assert_eq!(coinbase.block_height(), BlockHeight::from_u32(NU7_1));
    assert_eq!(coinbase.coinbase_data(), b"zakura");
    assert_eq!(
        tx.v7_fields().unwrap().value_deltas,
        ValueDeltas {
            transparent: -ZatBalance::const_from_i64(miner_reward(fees, nsm) as i64),
            coinbase: ZatBalance::const_from_i64(312_500_000 - 37_500_000 - 6_000),
            fee: ZatBalance::const_from_i64(10_000),
        }
    );
    assert_eq!(delta_sum(&tx), 0);
    assert_eq!(
        tx.fee_paid(|_| -> Result<_, zcash_protocol::value::BalanceError> {
            unreachable!("a coinbase transaction spends nothing")
        }),
        Ok(Some(Zatoshis::ZERO))
    );
}

#[test]
fn v7_coinbase_builder_rejects_inconsistent_inputs() {
    let (fees, nsm) = (10_000, 6_000);
    let reward = miner_reward(fees, nsm);
    assert_matches!(
        build_coinbase(coinbase_builder(v7_coinbase(fees, nsm), reward - 1)),
        Err(Error::ChangeRequired(_))
    );
    assert_matches!(
        build_coinbase(coinbase_builder(v7_coinbase(fees, nsm), reward + 1)),
        Err(Error::InsufficientFunds(_))
    );
    assert_matches!(
        build_coinbase(coinbase_builder(v7_coinbase(fees, fees + 1), reward)),
        Err(Error::NsmFeeContributionExceedsFees)
    );
    let mut overdrawn = v7_coinbase(fees, nsm);
    overdrawn.lockbox_value = Zatoshis::const_from_u64(312_500_001);
    assert_matches!(
        build_coinbase(coinbase_builder(overdrawn, reward)),
        Err(Error::V7Coinbase(CoinbaseError::LockboxExceedsSubsidy))
    );
    let mut chatty = v7_coinbase(fees, nsm);
    chatty.coinbase_data = vec![0; 95];
    assert_matches!(
        build_coinbase(coinbase_builder(chatty, reward)),
        Err(Error::V7Coinbase(CoinbaseError::CoinbaseDataTooLong))
    );

    // Before NU7.1 a v7 coinbase transaction is not valid.
    let early = Builder::new(
        network(),
        (NU7_1 - 1).into(),
        BuildConfig::V7Coinbase(v7_coinbase(fees, nsm)),
    );
    assert_matches!(
        build_coinbase(early),
        Err(Error::TargetIncompatible(
            BranchId::Nu7,
            TxVersion::V7,
            None
        ))
    );

    // The coinbase configuration fixes the version.
    let mut legacy = Builder::new(
        network(),
        NU7_1.into(),
        BuildConfig::Coinbase { miner_data: None },
    );
    assert_matches!(
        legacy.propose_version::<Infallible>(TxVersion::V7),
        Err(Error::CoinbaseVersionMismatch(TxVersion::V7))
    );
    let mut v7 = coinbase_builder(v7_coinbase(fees, nsm), reward);
    assert_matches!(
        v7.propose_version::<Infallible>(TxVersion::V6),
        Err(Error::CoinbaseVersionMismatch(TxVersion::V6))
    );
}

/// A v7 coinbase transaction spends nothing, so the builder refuses transparent inputs
/// instead of building a transaction that breaks the bundle-local rules.
#[cfg(feature = "transparent-inputs")]
#[test]
fn v7_coinbase_builder_rejects_transparent_inputs() {
    use ::transparent::{
        builder::TransparentSigningSet,
        bundle::{OutPoint, TxOut},
        keys::{AccountPrivKey, NonHardenedChildIndex},
    };
    use zip32::AccountId;

    let (fees, nsm) = (10_000, 6_000);
    let mut builder = coinbase_builder(v7_coinbase(fees, nsm), miner_reward(fees, nsm));
    let tsk = AccountPrivKey::from_seed(&network(), &[0u8; 32], AccountId::ZERO).unwrap();
    let pubkey = TransparentSigningSet::new().add_key(
        tsk.derive_external_secret_key(NonHardenedChildIndex::ZERO)
            .unwrap(),
    );
    let prev_coin = TxOut::new(
        Zatoshis::const_from_u64(50_000),
        TransparentAddress::from_pubkey(&pubkey).script().into(),
    );
    builder
        .add_transparent_p2pkh_input(pubkey, OutPoint::fake(), prev_coin)
        .unwrap();
    assert_matches!(
        build_coinbase(builder),
        Err(Error::Coinbase(
            ::transparent::coinbase::Error::UnexpectedInputs
        ))
    );
}

/// The coinbase bundle's delta can be negative, when the ZIP 235 fee contribution
/// exceeds what is left of the subsidy after the lockbox deposit.
#[test]
fn v7_coinbase_delta_can_be_negative() {
    let mut config = V7CoinbaseConfig::new(
        Zatoshis::const_from_u64(1_000),
        Zatoshis::ZERO,
        Zatoshis::const_from_u64(10_000),
        Zatoshis::const_from_u64(6_000),
    );
    config.miner_poll = Some(
        crate::transaction::v7::MinerPoll::new(
            vec![crate::transaction::v7::MinerSignal {
                signal_code: 4,
                level_of_support: 2,
            }],
            [9; 16],
        )
        .unwrap(),
    );
    let tx = build_coinbase(coinbase_builder(config.clone(), 1_000 + 10_000 - 6_000)).unwrap();
    let tx = round_trip(&tx);
    assert_eq!(
        tx.v7_fields().unwrap().value_deltas.coinbase,
        ZatBalance::const_from_i64(-5_000)
    );
    assert_eq!(delta_sum(&tx), 0);
    assert_eq!(
        tx.coinbase_bundle().unwrap().miner_poll(),
        config.miner_poll.as_ref()
    );
}

/// A v7 coinbase transaction can pay its miner in the Ironwood pool, whose dummy spends
/// and binding signature sign their own v7 digests.
#[test]
fn v7_coinbase_with_ironwood_reward_verifies() {
    use crate::transaction::{
        components::orchard, sighash::V7SignatureHashes, v7::ShieldedBundleType,
    };
    use zcash_protocol::memo::MemoBytes;

    let (fees, nsm) = (10_000, 6_000);
    let reward = miner_reward(fees, nsm);
    let mut builder = coinbase_builder(v7_coinbase(fees, nsm), reward - 100_000);
    let recipient = ::orchard::keys::FullViewingKey::from(
        &::orchard::keys::SpendingKey::from_bytes([0; 32]).unwrap(),
    )
    .address_at(0u32, ::orchard::keys::Scope::External);
    builder
        .add_ironwood_output::<Infallible>(
            None,
            recipient,
            Zatoshis::const_from_u64(100_000),
            MemoBytes::empty(),
        )
        .unwrap();
    let tx = round_trip(&build_coinbase(builder).unwrap());
    assert_eq!(delta_sum(&tx), 0);
    let ironwood = tx.ironwood_bundle().unwrap();
    assert_eq!(i64::from(*ironwood.value_balance()), -100_000);

    let verifying = super::transaction::with_spent_outputs(
        &tx,
        super::transaction::SpentOutputs {
            reads: Default::default(),
            amounts: vec![],
            script_pubkeys: vec![],
        },
    );
    let sighashes = V7SignatureHashes::new(&verifying)
        .unwrap()
        .shielded_sighashes(ShieldedBundleType::Ironwood)
        .unwrap();
    let vk = ::orchard::circuit::VerifyingKey::build(
        orchard::bundle_version_for_branch(BranchId::Nu7_1, ::orchard::ValuePool::Ironwood)
            .unwrap()
            .circuit_version(),
    );
    let mut validator = ::orchard::bundle::BatchValidator::new(&vk);
    validator.add_bundle(ironwood, &sighashes).unwrap();
    assert!(validator.validate(thread_rng()));
}

#[cfg(feature = "pczt")]
#[test]
fn pczt_does_not_support_v7() {
    let mut builder = Builder::new(network(), NU7_1.into(), standard(None));
    builder
        .propose_version::<Infallible>(TxVersion::V7)
        .unwrap();
    assert_matches!(
        builder.build_for_pczt(
            thread_rng(),
            &crate::transaction::fees::zip317::FeeRule::standard()
        ),
        Err(Error::PcztUnsupported(TxVersion::V7))
    );
}

/// `sign` signs each real Sapling spend over the digest for its own position.
#[test]
fn sapling_spends_sign_their_own_digests() {
    use ::sapling::{Node, Rseed, zip32::ExtendedSpendingKey};
    use incrementalmerkletree::{frontier::CommitmentTree, witness::IncrementalWitness};
    use rand::RngExt;
    use sapling::bundle::SignatureDigests;

    use super::transaction::{SpentOutputs, with_spent_outputs};
    use crate::transaction::{sighash::V7SignatureHashes, v7::ShieldedBundleType};
    use ::transparent::builder::TransparentSigningSet;

    let mut rng = thread_rng();
    let extsk = ExtendedSpendingKey::master(&[]);
    let dfvk = extsk.to_diversifiable_full_viewing_key();
    let to = dfvk.default_address().1;
    let notes = [40_000, 30_000].map(|value| {
        to.create_note(
            ::sapling::value::NoteValue::from_raw(value),
            Rseed::AfterZip212(rng.random()),
        )
    });
    let mut tree = CommitmentTree::<Node, 32>::empty();
    tree.append(Node::from_cmu(&notes[0].cmu())).unwrap();
    let mut witness0 = IncrementalWitness::from_tree(tree.clone()).unwrap();
    tree.append(Node::from_cmu(&notes[1].cmu())).unwrap();
    witness0.append(Node::from_cmu(&notes[1].cmu())).unwrap();
    let witness1 = IncrementalWitness::from_tree(tree).unwrap();

    let mut builder = Builder::new(
        network(),
        NU7_1.into(),
        BuildConfig::Standard {
            sapling_anchor: Some(witness0.root().into()),
            orchard_anchor: None,
            ironwood_anchor: None,
            orchard_padding: BundlePadding::DEFAULT,
            ironwood_padding: BundlePadding::DEFAULT,
        },
    );
    builder
        .propose_version::<Infallible>(TxVersion::V7)
        .unwrap();
    for (note, witness) in notes.iter().zip([&witness0, &witness1]) {
        builder
            .add_sapling_spend::<Infallible>(
                dfvk.fvk().clone(),
                note.clone(),
                witness.path().unwrap(),
            )
            .unwrap();
    }
    // Two Sapling spends with two padded outputs, and one transparent output, are three
    // logical actions under ZIP 317.
    builder
        .add_transparent_output(
            &TransparentAddress::PublicKeyHash([0; 20]),
            Zatoshis::const_from_u64(70_000 - 15_000),
        )
        .unwrap();
    let tx = builder
        .mock_build(&TransparentSigningSet::new(), &[extsk], &[], thread_rng())
        .unwrap()
        .transaction()
        .clone();
    let tx = round_trip(&tx);
    assert_eq!(delta_sum(&tx), 0);

    let verifying = with_spent_outputs(
        &tx,
        SpentOutputs {
            reads: Default::default(),
            amounts: vec![],
            script_pubkeys: vec![],
        },
    );
    let sighashes = V7SignatureHashes::new(&verifying)
        .unwrap()
        .shielded_sighashes(ShieldedBundleType::Sapling)
        .unwrap();
    let spends = tx.sapling_bundle().unwrap().shielded_spends();
    assert_eq!(spends.len(), 2);
    for (index, spend) in spends.iter().enumerate() {
        for position in 0..spends.len() {
            assert_eq!(
                spend
                    .rk()
                    .verify(
                        &sighashes.spend_auth(position).unwrap(),
                        spend.spend_auth_sig()
                    )
                    .is_ok(),
                position == index,
                "spend {index} checked against the digest for position {position}"
            );
        }
    }
}
