//! Tests of typed v7 transactions: their encoding, transaction identifier, authorizing
//! data commitment, and signature digests.

// The tests use `std` even when the crate is built without it.
extern crate std;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Write as _;

use proptest::{
    prelude::*,
    strategy::ValueTree,
    test_runner::{Config, TestRunner},
};

use ::transparent::{
    address::Script,
    bundle::{self as transparent, TxIn},
    sighash::{
        SighashType, SignableInput as TransparentSignableInput, TransparentAuthorizingContext,
    },
};
use zcash_protocol::{
    consensus::{BlockHeight, BranchId},
    value::{ZatBalance, Zatoshis},
};

use crate::transaction::{
    Authorization, Authorized, Transaction, TransactionData, TxDigests, TxIdDigester, TxVersion,
    components::{orchard::testing as orchard_testing, sapling::testing as sapling_testing},
    sighash::{SighashError, SignableInput, signature_hash},
    v7::{
        BundleData, BundleId, BundleType, BundleVariant, CoinbaseBundle, Envelope, MinerPoll,
        MinerSignal, ShieldedBundleType, ShieldedSignature, V7Fields, ValueDeltas, ValuePoolDelta,
    },
};

/// A transparent authorizing context that knows the spent outputs, as a verifier would.
#[derive(Debug)]
pub(super) struct SpentOutputs {
    pub(super) reads: core::cell::Cell<usize>,
    pub(super) amounts: Vec<Zatoshis>,
    pub(super) script_pubkeys: Vec<Script>,
}

impl transparent::Authorization for SpentOutputs {
    type ScriptSig = Script;
}

impl TransparentAuthorizingContext for SpentOutputs {
    fn input_amounts(&self) -> Vec<Zatoshis> {
        self.reads.set(self.reads.get() + 1);
        self.amounts.clone()
    }

    fn input_scriptpubkeys(&self) -> Vec<Script> {
        self.reads.set(self.reads.get() + 1);
        self.script_pubkeys.clone()
    }
}

pub(super) struct Verifying;

impl Authorization for Verifying {
    type TransparentAuth = SpentOutputs;
    type SaplingAuth = sapling::bundle::Authorized;
    type OrchardAuth = orchard::bundle::Authorized;
}

/// Pairs a parsed transaction with the outputs its transparent inputs spend.
pub(super) fn with_spent_outputs(
    tx: &TransactionData<Authorized>,
    spent: SpentOutputs,
) -> TransactionData<Verifying> {
    let transparent = tx.transparent_bundle().map(|b| transparent::Bundle {
        vin: b
            .vin
            .iter()
            .map(|txin| {
                TxIn::from_parts(
                    txin.prevout().clone(),
                    txin.script_sig().clone(),
                    txin.sequence(),
                )
            })
            .collect(),
        vout: b.vout.clone(),
        authorization: spent,
    });
    TransactionData::from_parts_v7(
        tx.consensus_branch_id(),
        tx.lock_time(),
        tx.expiry_height(),
        transparent,
        tx.sapling_bundle().cloned(),
        tx.orchard_bundle().cloned(),
        tx.ironwood_bundle().cloned(),
        tx.v7_fields().cloned().expect("a v7 transaction"),
    )
    .expect("the parts come from a v7 transaction, which satisfies the bundle-local rules")
}

/// The digest of every signature a v7 transaction can carry, with a label naming it.
pub(super) fn all_signature_digests(
    tx: &TransactionData<Verifying>,
    txid_parts: &TxDigests<blake2b_simd::Hash>,
) -> Vec<(String, [u8; 32])> {
    let mut digests = Vec::new();
    let prepared = crate::transaction::sighash::V7SignatureHashes::new(tx).unwrap();
    if let Some(bundle) = tx.transparent_bundle() {
        let amounts = bundle.authorization.input_amounts();
        let scripts = bundle.authorization.input_scriptpubkeys();
        for index in 0..bundle.vin.len() {
            let input = TransparentSignableInput::from_parts(
                bundle,
                SighashType::ALL,
                index,
                &scripts[index],
                &scripts[index],
                amounts[index],
            )
            .unwrap();
            let signer = SignableInput::Transparent(input);
            let digest = prepared.signature_hash(&signer).unwrap();
            assert_eq!(
                digest.as_ref(),
                signature_hash(tx, &signer, txid_parts).unwrap().as_ref()
            );
            digests.push((alloc::format!("t {index}"), *digest.as_ref()));
        }
    }
    let shielded = [
        (
            ShieldedBundleType::Sapling,
            tx.sapling_bundle().map(|b| b.shielded_spends().len()),
        ),
        (
            ShieldedBundleType::Orchard,
            tx.orchard_bundle().map(|b| b.actions().len()),
        ),
        (
            ShieldedBundleType::Ironwood,
            tx.ironwood_bundle().map(|b| b.actions().len()),
        ),
    ];
    for (bundle_type, count) in shielded {
        let Some(count) = count else { continue };
        let signatures = (0..count)
            .map(|index| ShieldedSignature::SpendAuth { index })
            .chain([ShieldedSignature::Binding]);
        for signature in signatures {
            let signer = SignableInput::V7Shielded {
                bundle_type,
                signature,
            };
            let digest = prepared.signature_hash(&signer).unwrap();
            assert_eq!(
                digest.as_ref(),
                signature_hash(tx, &signer, txid_parts).unwrap().as_ref()
            );
            let position = match signature {
                ShieldedSignature::SpendAuth { index } => alloc::format!("{index}"),
                ShieldedSignature::Binding => "b".into(),
            };
            digests.push((
                alloc::format!("s {} {position}", BundleType::from(bundle_type).id()),
                *digest.as_ref(),
            ));
        }
    }
    digests
}

/// Arbitrary bundles with enough inputs, outputs, spends, and actions to cut any vector
/// from. Their proofs and signatures do not verify, which the digests do not depend on.
#[derive(Debug)]
struct VectorParts {
    transparent: transparent::Bundle<transparent::Authorized>,
    sapling: sapling::Bundle<sapling::bundle::Authorized, ZatBalance>,
    orchard: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
    ironwood: orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
}

prop_compose! {
    fn arb_vector_parts()(
        transparent in transparent::testing::arb_bundle()
            .prop_filter_map("needs 3 inputs and 2 outputs", |b| {
                b.filter(|b| b.vin.len() >= 3 && b.vout.len() >= 2)
            }),
        sapling in sapling_testing::arb_bundle_for_version(TxVersion::V7)
            .prop_filter_map("needs 2 spends and 2 outputs", |b| {
                b.filter(|b| b.shielded_spends().len() >= 2 && b.shielded_outputs().len() >= 2)
            }),
        orchard in orchard_testing::arb_bundle_for_version(TxVersion::V7)
            .prop_filter_map("needs 2 actions", |b| b.filter(|b| b.actions().len() >= 2)),
        ironwood in orchard_testing::arb_ironwood_bundle_for_version(TxVersion::V7)
            .prop_filter_map("needs 2 actions", |b| b.filter(|b| b.actions().len() >= 2)),
    ) -> VectorParts {
        VectorParts { transparent, sapling, orchard, ironwood }
    }
}

/// The shape of a vector: which bundles it has, how large they are, and the values they
/// move. Every vector is shaped like a transaction consensus could accept: its deltas
/// balance, a coinbase transaction spends nothing, and it uses no NSM delta. ZIP 248 only
/// says that registration does not activate a bundle; that NU7.1 does not activate the
/// NSM bundle is an assumption of this implementation.
struct Shape {
    lock_time: u32,
    expiry_height: u32,
    /// The values of the outputs that the transparent inputs spend.
    spent: &'static [u64],
    /// The values of the transparent outputs.
    outputs: &'static [u64],
    /// The number of Sapling spends and outputs, and the Sapling value balance.
    sapling: Option<(usize, usize, i64)>,
    /// The Orchard value balance, which consensus requires to be nonnegative.
    orchard: Option<i64>,
    /// The Ironwood value balance, and whether the bundle enables cross-address
    /// transfers, which the Ironwood pool leaves to the transaction.
    ironwood: Option<(i64, bool)>,
    /// The coinbase bundle and its delta.
    coinbase: Option<(CoinbaseBundle, i64)>,
    fee: i64,
}

/// A spend from every pool, with two of everything.
fn standard_shape() -> Shape {
    Shape {
        lock_time: 0,
        expiry_height: 3_000_040,
        spent: &[2_000_000, 500_000],
        outputs: &[1_000_000, 250_000],
        sapling: Some((2, 2, -300_000)),
        orchard: Some(200_000),
        ironwood: Some((-1_130_000, true)),
        coinbase: None,
        fee: -20_000,
    }
}

/// Three transparent inputs shielded into Ironwood.
fn shielding_shape() -> Shape {
    Shape {
        lock_time: 2_999_990,
        expiry_height: 3_000_040,
        spent: &[100_000, 200_000, 300_000],
        outputs: &[],
        sapling: None,
        orchard: None,
        ironwood: Some((-575_000, false)),
        coinbase: None,
        fee: -25_000,
    }
}

/// Two Sapling spends paying two transparent outputs, with no Sapling outputs.
fn deshielding_shape() -> Shape {
    Shape {
        lock_time: 0,
        expiry_height: 0,
        spent: &[],
        outputs: &[600_000, 380_000],
        sapling: Some((2, 0, 1_000_000)),
        orchard: None,
        ironwood: None,
        coinbase: None,
        fee: -20_000,
    }
}

/// The block subsidy and lockbox deposit of the coinbase vectors.
const SUBSIDY: u64 = 156_250_000;
const LOCKBOX: u64 = 18_750_000;

/// A coinbase transaction with miner data and a poll response, paying transparent,
/// Sapling, and Ironwood outputs, and collecting fees less the ZIP 235 contribution.
fn rich_coinbase_shape() -> Shape {
    let height = 3_000_000;
    let (fees, nsm_contribution): (u64, u64) = (60_000, 36_000);
    let poll = MinerPoll::new(
        vec![
            MinerSignal {
                signal_code: 1,
                level_of_support: 2,
            },
            MinerSignal {
                signal_code: 7,
                level_of_support: 0,
            },
            MinerSignal {
                signal_code: 200,
                level_of_support: 255,
            },
        ],
        [0x5a; 16],
    )
    .unwrap();
    let coinbase = CoinbaseBundle::new(
        BlockHeight::from_u32(height),
        Zatoshis::const_from_u64(SUBSIDY),
        Zatoshis::const_from_u64(LOCKBOX),
        b"/zakura:1.9.0/ ZIP 248 test vector".to_vec(),
        Some(poll),
    )
    .unwrap();
    let coinbase_delta = SUBSIDY - LOCKBOX - nsm_contribution;
    Shape {
        lock_time: 0,
        expiry_height: height,
        spent: &[],
        outputs: &[100_000_000, 7_524_000],
        sapling: Some((0, 1, -10_000_000)),
        orchard: None,
        ironwood: Some((-20_000_000, true)),
        coinbase: Some((coinbase, i64::try_from(coinbase_delta).unwrap())),
        fee: i64::try_from(fees).unwrap(),
    }
}

/// A coinbase transaction in a block without other transactions, paying one transparent
/// output.
fn minimal_coinbase_shape() -> Shape {
    let height = 3_000_001;
    let coinbase = CoinbaseBundle::new(
        BlockHeight::from_u32(height),
        Zatoshis::const_from_u64(SUBSIDY),
        Zatoshis::const_from_u64(LOCKBOX),
        Vec::new(),
        None,
    )
    .unwrap();
    Shape {
        lock_time: 0,
        expiry_height: height,
        spent: &[],
        outputs: &[SUBSIDY - LOCKBOX],
        sapling: None,
        orchard: None,
        ironwood: None,
        coinbase: Some((coinbase, i64::try_from(SUBSIDY - LOCKBOX).unwrap())),
        fee: 0,
    }
}

/// A script public key shaped like a P2PKH output's for an even `seed`, and like a P2SH
/// output's for an odd one, distinct for each `seed`.
fn script_pubkey(seed: u8) -> Script {
    let hash = (0..20).map(|i| seed.wrapping_mul(31).wrapping_add(i));
    let script = if seed.is_multiple_of(2) {
        [vec![0x76, 0xa9, 0x14], hash.collect(), vec![0x88, 0xac]].concat()
    } else {
        [vec![0xa9, 0x14], hash.collect(), vec![0x87]].concat()
    };
    Script(zcash_script::script::Code(script))
}

/// Cuts a transaction of `shape` from `parts`, with the outputs its inputs spend.
fn shaped_tx(parts: &VectorParts, shape: Shape) -> (Transaction, SpentOutputs) {
    let balance = |value: i64| ZatBalance::from_i64(value).unwrap();
    let zats = |value: u64| Zatoshis::from_u64(value).unwrap();

    let transparent = transparent::Bundle {
        vin: parts.transparent.vin[..shape.spent.len()].to_vec(),
        vout: shape
            .outputs
            .iter()
            .zip(0..)
            .map(|(value, seed)| transparent::TxOut::new(zats(*value), script_pubkey(seed)))
            .collect(),
        authorization: transparent::Authorized,
    };
    let spent = SpentOutputs {
        reads: Default::default(),
        amounts: shape.spent.iter().map(|v| zats(*v)).collect(),
        script_pubkeys: (0..shape.spent.len())
            .map(|i| script_pubkey(100 + u8::try_from(i).unwrap()))
            .collect(),
    };
    let total = |values: &[u64]| i64::try_from(values.iter().sum::<u64>()).unwrap();
    let transparent_delta = total(shape.spent) - total(shape.outputs);

    let sapling = shape.sapling.and_then(|(spends, outputs, value_balance)| {
        sapling::Bundle::from_parts(
            parts.sapling.shielded_spends()[..spends].to_vec(),
            parts.sapling.shielded_outputs()[..outputs].to_vec(),
            balance(value_balance),
            *parts.sapling.authorization(),
        )
    });
    // Every bundle pays outputs. A coinbase transaction's Orchard-protocol bundles have
    // spends disabled, and the others enable them.
    let spends_enabled = shape.coinbase.is_none();
    let orchard_protocol = |bundle: &orchard::Bundle<orchard::bundle::Authorized, ZatBalance>,
                            value_balance: i64,
                            cross_address: bool| {
        let actions = bundle.actions().iter().take(2).cloned().collect::<Vec<_>>();
        let proof = &bundle.authorization().proof().as_ref()[..2720 + 2272 * actions.len()];
        let version = bundle.bundle_version();
        let flags = u8::from(cross_address) << 2 | 0b10 | u8::from(spends_enabled);
        orchard::Bundle::try_from_parts(
            nonempty::NonEmpty::from_vec(actions).unwrap(),
            orchard::bundle::Flags::from_byte(flags, version).unwrap(),
            balance(value_balance),
            *bundle.anchor(),
            orchard::bundle::Authorized::from_parts(
                orchard::Proof::new(proof.to_vec()),
                bundle.authorization().binding_signature().clone(),
            ),
            version,
        )
        .unwrap()
    };

    let (coinbase_bundle, coinbase_delta) = shape
        .coinbase
        .map_or((None, 0), |(bundle, delta)| (Some(bundle), delta));
    let fields = V7Fields {
        value_deltas: ValueDeltas {
            transparent: balance(transparent_delta),
            coinbase: balance(coinbase_delta),
            fee: balance(shape.fee),
            ..ValueDeltas::default()
        },
        coinbase_bundle,
    };

    let tx = TransactionData::from_parts_v7(
        BranchId::Nu7_1,
        shape.lock_time,
        BlockHeight::from_u32(shape.expiry_height),
        Some(transparent),
        sapling,
        // The Orchard pool requires `enableCrossAddress = 0`.
        shape
            .orchard
            .map(|v| orchard_protocol(&parts.orchard, v, false)),
        shape
            .ironwood
            .map(|(v, cross_address)| orchard_protocol(&parts.ironwood, v, cross_address)),
        fields,
    )
    .expect("the shapes satisfy the bundle-local rules")
    .freeze()
    .unwrap();
    assert_eq!(
        tx.value_pool_deltas()
            .unwrap()
            .iter()
            .map(|d| d.value.get())
            .sum::<i64>(),
        0,
        "the shapes balance"
    );
    (tx, spent)
}

/// Writes the vector transactions with their digests for the independent Python oracle,
/// to the file named by `V7_VECTOR_DUMP`. The frozen vectors in `vectors.rs` were made
/// this way; `scripts/zip248/README.md` describes how to check and format them.
#[test]
#[ignore = "generates vectors for the Python oracle"]
fn dump_vectors_for_oracle() {
    let mut runner = TestRunner::new_with_rng(
        Config::default(),
        proptest::test_runner::TestRng::deterministic_rng(
            proptest::test_runner::RngAlgorithm::ChaCha,
        ),
    );
    let mut out = String::new();
    for shape in [
        standard_shape(),
        shielding_shape(),
        deshielding_shape(),
        rich_coinbase_shape(),
        minimal_coinbase_shape(),
    ] {
        let parts = arb_vector_parts().new_tree(&mut runner).unwrap().current();
        let (tx, spent) = shaped_tx(&parts, shape);
        let mut bytes = Vec::new();
        tx.write(&mut bytes).unwrap();
        writeln!(out, "TX {}", hex::encode(&bytes)).unwrap();
        writeln!(
            out,
            "AMOUNTS {}",
            spent
                .amounts
                .iter()
                .map(|a| alloc::format!("{}", a.into_u64()))
                .collect::<Vec<_>>()
                .join(",")
        )
        .unwrap();
        writeln!(
            out,
            "SCRIPTS {}",
            spent
                .script_pubkeys
                .iter()
                .map(|s| hex::encode(&s.0.0))
                .collect::<Vec<_>>()
                .join(",")
        )
        .unwrap();
        writeln!(out, "TXID {}", hex::encode(tx.txid().as_ref())).unwrap();
        writeln!(out, "AUTH {}", hex::encode(tx.auth_commitment().as_bytes())).unwrap();
        let verifying = with_spent_outputs(&tx, spent);
        let txid_parts = verifying.digest(TxIdDigester);
        for (label, digest) in all_signature_digests(&verifying, &txid_parts) {
            writeln!(out, "SIG {label} {}", hex::encode(digest)).unwrap();
        }
        writeln!(out, "END").unwrap();
    }
    std::fs::write(std::env::var("V7_VECTOR_DUMP").unwrap(), out).unwrap();
}

fn verifying_vector(tv: &super::vectors::TestVector) -> (Transaction, TransactionData<Verifying>) {
    let bytes = hex::decode(tv.tx.as_bytes()).unwrap();
    let tx = Transaction::read(&bytes[..], BranchId::Nu7_1).unwrap();
    let spent = SpentOutputs {
        reads: Default::default(),
        amounts: tv
            .amounts
            .iter()
            .map(|a| Zatoshis::from_u64(*a).unwrap())
            .collect(),
        script_pubkeys: tv
            .script_pubkeys
            .iter()
            .map(|s| Script(zcash_script::script::Code(hex::decode(s).unwrap())))
            .collect(),
    };
    let verifying = with_spent_outputs(&tx, spent);
    (tx, verifying)
}

#[test]
fn vectors_match() {
    for tv in super::vectors::TEST_VECTORS {
        let (tx, verifying) = verifying_vector(tv);
        assert_eq!(hex::encode(tx.txid().as_ref()), tv.txid, "{}", tv.bundles);
        assert_eq!(hex::encode(tx.auth_commitment().as_bytes()), tv.auth_digest);

        let mut written = Vec::new();
        tx.write(&mut written).unwrap();
        assert_eq!(hex::encode(&written), tv.tx);

        let txid_parts = verifying.digest(TxIdDigester);
        let digests = all_signature_digests(&verifying, &txid_parts);
        assert_eq!(digests.len(), tv.sighashes.len());
        for ((label, digest), (expected_label, expected)) in digests.iter().zip(tv.sighashes) {
            assert_eq!(label, expected_label);
            assert_eq!(&hex::encode(digest), expected, "{label} in {}", tv.bundles);
        }
    }
}

/// The vector with a transparent input, a Sapling spend, and an Orchard and an Ironwood
/// bundle with spends enabled.
const STANDARD: usize = 0;
/// The vector with transparent inputs and Ironwood outputs, and no Sapling bundle.
const SHIELDING: usize = 1;
/// The vector with two Sapling spends and no other spends.
const DESHIELDING: usize = 2;
/// The coinbase vector with a poll response and Sapling and Ironwood outputs.
const RICH_COINBASE: usize = 3;
/// The coinbase vector with only a transparent output, and so no authorizing data.
const MINIMAL_COINBASE: usize = 4;

/// Re-encodes the vector at `index` after `edit` changes its envelope, and decodes it as a
/// typed transaction.
fn decode_edited(
    index: usize,
    edit: impl FnOnce(&mut Vec<ValuePoolDelta>, &mut Vec<BundleData>, &mut Vec<BundleData>),
) -> std::io::Result<TransactionData<Authorized>> {
    let bytes = hex::decode(super::vectors::TEST_VECTORS[index].tx.as_bytes()).unwrap();
    let (header, mut deltas, mut effects, mut auths) =
        Envelope::read(&bytes[..]).unwrap().into_parts();
    edit(&mut deltas, &mut effects, &mut auths);
    let mut edited = Vec::new();
    Envelope::new(header, deltas, effects, auths)
        .unwrap()
        .write(&mut edited)
        .unwrap();
    TransactionData::read(&edited[..], BranchId::Nu7_1)
}

fn position(map: &[BundleData], bundle_type: BundleType) -> usize {
    map.iter()
        .position(|b| b.bundle.bundle_type == bundle_type)
        .unwrap()
}

#[test]
fn typed_decoding_rejects_invalid_bundles() {
    // The unmodified vectors decode.
    for index in 0..super::vectors::TEST_VECTORS.len() {
        decode_edited(index, |_, _, _| {}).unwrap();
    }

    let unregistered = BundleId::new(BundleType::new(7), BundleVariant::V0);
    type Edit =
        Box<dyn FnOnce(&mut Vec<ValuePoolDelta>, &mut Vec<BundleData>, &mut Vec<BundleData>)>;
    let coinbase_effect = Envelope::read(
        &hex::decode(super::vectors::TEST_VECTORS[RICH_COINBASE].tx.as_bytes()).unwrap()[..],
    )
    .unwrap()
    .effect_bundle(BundleType::COINBASE)
    .unwrap()
    .clone();
    let add_coinbase = |coinbase: BundleData| -> Edit {
        Box::new(move |_, e, _| {
            let at = e.partition_point(|b| b.bundle.bundle_type < BundleType::COINBASE);
            e.insert(at, coinbase);
        })
    };
    let cases: Vec<(usize, &str, &str, Edit)> = vec![
        (
            STANDARD,
            "unregistered bundle",
            "is not registered",
            Box::new(move |d, _, _| {
                d.push(ValuePoolDelta {
                    bundle: unregistered,
                    value: core::num::NonZeroI64::new(1).unwrap(),
                })
            }),
        ),
        (
            STANDARD,
            "unregistered variant",
            "is not registered",
            Box::new(|d, e, a| {
                for id in d
                    .iter_mut()
                    .map(|d| &mut d.bundle)
                    .filter(|id| id.bundle_type == BundleType::SAPLING)
                {
                    id.variant = BundleVariant::new(1);
                }
                let i = position(e, BundleType::SAPLING);
                e[i].bundle.variant = BundleVariant::new(1);
                let i = position(a, BundleType::SAPLING);
                a[i].bundle.variant = BundleVariant::new(1);
            }),
        ),
        (
            STANDARD,
            "fee bundle with effecting data",
            "does not permit this map entry",
            Box::new(|_, e, _| {
                e.push(BundleData {
                    bundle: BundleId::FEE,
                    data: Vec::new(),
                })
            }),
        ),
        (
            STANDARD,
            "transparent inputs without authorizing data",
            "type 0 needs authorizing data",
            Box::new(|_, _, a| {
                a.remove(position(a, BundleType::TRANSPARENT));
            }),
        ),
        (
            STANDARD,
            "Sapling effects without authorizing data",
            "type 2 needs authorizing data",
            Box::new(|_, _, a| {
                a.remove(position(a, BundleType::SAPLING));
            }),
        ),
        (
            STANDARD,
            "Sapling balance without its bundle",
            "bundle type 2 has no effecting bundle",
            Box::new(|_, e, a| {
                a.remove(position(a, BundleType::SAPLING));
                e.remove(position(e, BundleType::SAPLING));
            }),
        ),
        (
            STANDARD,
            "non-zero sighash variant",
            "sighash variant 0",
            Box::new(|_, _, a| {
                // The first input's sighashInfo is the first two bytes: length 1, variant 0.
                let i = position(a, BundleType::TRANSPARENT);
                a[i].data[1] = 1;
            }),
        ),
        (
            STANDARD,
            "sighashInfo with associated data",
            "sighash variant 0",
            Box::new(|_, _, a| {
                let i = position(a, BundleType::ORCHARD);
                // An anchor, then the proof for the bundle's two actions with a
                // three-byte compactSize length prefix, then the first action's
                // sighashInfo.
                let at = 32 + 3 + 2720 + 2 * 2272;
                a[i].data[at] = 2;
                a[i].data.insert(at + 2, 0xff);
            }),
        ),
        (
            RICH_COINBASE,
            "trailing byte in a payload",
            "trailing bytes",
            Box::new(|_, e, _| {
                let i = position(e, BundleType::COINBASE);
                e[i].data.push(0);
            }),
        ),
        (
            RICH_COINBASE,
            "coinbase height zero",
            "blockHeight is out of range",
            Box::new(|_, e, _| {
                let i = position(e, BundleType::COINBASE);
                e[i].data[..4].copy_from_slice(&0u32.to_le_bytes());
            }),
        ),
        (
            STANDARD,
            "transparent delta without its bundle",
            "bundle type 0 has no effecting bundle",
            Box::new(|_, e, a| {
                a.remove(position(a, BundleType::TRANSPARENT));
                e.remove(position(e, BundleType::TRANSPARENT));
            }),
        ),
        (
            RICH_COINBASE,
            "coinbase delta without its bundle",
            "bundle type 1 has no effecting bundle",
            Box::new(|_, e, _| {
                e.remove(position(e, BundleType::COINBASE));
            }),
        ),
        (
            STANDARD,
            "coinbase bundle with transparent inputs",
            "coinbase transaction spends from bundle type 0",
            add_coinbase(coinbase_effect.clone()),
        ),
        (
            DESHIELDING,
            "coinbase bundle with Sapling spends",
            "coinbase transaction spends from bundle type 2",
            add_coinbase(coinbase_effect.clone()),
        ),
    ];
    for (index, name, reason, edit) in cases {
        let error = decode_edited(index, edit).expect_err(name);
        assert!(
            alloc::string::ToString::to_string(&error).contains(reason),
            "{name} was rejected for another reason: {error}"
        );
    }
}

#[test]
fn from_parts_v7_enforces_the_bundle_local_rules() {
    use crate::transaction::v7::BundleRuleError;

    let read = |index: usize| {
        let tv = &super::vectors::TEST_VECTORS[index];
        Transaction::read(&hex::decode(tv.tx.as_bytes()).unwrap()[..], BranchId::Nu7_1)
            .unwrap()
            .into_data()
    };
    let standard = read(STANDARD);
    let from_parts = |transparent, sapling, orchard, ironwood, fields| {
        TransactionData::<Authorized>::from_parts_v7(
            BranchId::Nu7_1,
            0,
            BlockHeight::from_u32(0),
            transparent,
            sapling,
            orchard,
            ironwood,
            fields,
        )
        .err()
    };

    // A coinbase transaction cannot spend from any pool.
    let coinbase = V7Fields {
        coinbase_bundle: read(RICH_COINBASE).coinbase_bundle().cloned(),
        ..V7Fields::default()
    };
    let pools = [
        (
            BundleType::TRANSPARENT,
            from_parts(
                standard.transparent_bundle().cloned(),
                None,
                None,
                None,
                coinbase.clone(),
            ),
        ),
        (
            BundleType::SAPLING,
            from_parts(
                None,
                standard.sapling_bundle().cloned(),
                None,
                None,
                coinbase.clone(),
            ),
        ),
        (
            BundleType::ORCHARD,
            from_parts(
                None,
                None,
                standard.orchard_bundle().cloned(),
                None,
                coinbase.clone(),
            ),
        ),
        (
            BundleType::IRONWOOD,
            from_parts(
                None,
                None,
                None,
                standard.ironwood_bundle().cloned(),
                coinbase.clone(),
            ),
        ),
    ];
    for (pool, error) in pools {
        assert_eq!(error, Some(BundleRuleError::CoinbaseSpends(pool)));
    }
    assert_eq!(from_parts(None, None, None, None, coinbase), None);

    // A transparent or coinbase delta needs its bundle. A transparent bundle without inputs
    // or outputs is omitted, so it does not count.
    let mut transparent = V7Fields::default();
    transparent.value_deltas.transparent = ZatBalance::const_from_i64(1);
    let empty = transparent::Bundle {
        vin: vec![],
        vout: vec![],
        authorization: transparent::Authorized,
    };
    assert_eq!(
        from_parts(Some(empty), None, None, None, transparent),
        Some(BundleRuleError::DeltaWithoutBundle(BundleType::TRANSPARENT))
    );
    let mut coinbase_delta = V7Fields::default();
    coinbase_delta.value_deltas.coinbase = ZatBalance::const_from_i64(1);
    assert_eq!(
        from_parts(None, None, None, None, coinbase_delta),
        Some(BundleRuleError::DeltaWithoutBundle(BundleType::COINBASE))
    );

    // An Orchard-protocol bundle has the version of its own pool, which fixes its flag
    // rules: an Ironwood bundle cannot stand in for an Orchard bundle, or the reverse.
    assert_eq!(
        from_parts(
            None,
            None,
            standard.ironwood_bundle().cloned(),
            None,
            V7Fields::default()
        ),
        Some(BundleRuleError::WrongBundleVersion(BundleType::ORCHARD))
    );
    assert_eq!(
        from_parts(
            None,
            None,
            None,
            standard.orchard_bundle().cloned(),
            V7Fields::default()
        ),
        Some(BundleRuleError::WrongBundleVersion(BundleType::IRONWOOD))
    );
}

#[test]
fn mixed_sapling_anchors_are_rejected_at_construction_and_freeze() {
    let bytes = hex::decode(super::vectors::TEST_VECTORS[DESHIELDING].tx.as_bytes()).unwrap();
    let tx = Transaction::read(&bytes[..], BranchId::Nu7_1)
        .unwrap()
        .into_data();
    let bundle = tx.sapling_bundle().unwrap();
    let [first, second] = bundle.shielded_spends() else {
        panic!("expected two Sapling spends")
    };
    assert_eq!(first.anchor(), second.anchor());
    let mixed = sapling::Bundle::from_parts(
        vec![
            first.clone(),
            sapling_testing::spend_with_anchor(second, *first.anchor() + jubjub::Base::from(1)),
        ],
        bundle.shielded_outputs().to_vec(),
        *bundle.value_balance(),
        *bundle.authorization(),
    );
    assert_eq!(
        TransactionData::<Authorized>::from_parts_v7(
            tx.consensus_branch_id(),
            tx.lock_time(),
            tx.expiry_height(),
            tx.transparent_bundle().cloned(),
            mixed.clone(),
            tx.orchard_bundle().cloned(),
            tx.ironwood_bundle().cloned(),
            tx.v7_fields().unwrap().clone()
        )
        .err(),
        Some(crate::transaction::v7::BundleRuleError::MixedSaplingAnchors),
    );
    let replaced = tx.map_bundles::<Authorized>(|t| t, |_| mixed, |o| o);
    assert_eq!(
        replaced.freeze().unwrap_err().kind(),
        std::io::ErrorKind::InvalidData
    );
}

/// Bundles replaced after construction are checked again when the data is frozen, so no
/// transaction breaks the bundle-local rules.
#[test]
fn freezing_checks_the_bundle_local_rules_again() {
    let tv = &super::vectors::TEST_VECTORS[STANDARD];
    let tx =
        Transaction::read(&hex::decode(tv.tx.as_bytes()).unwrap()[..], BranchId::Nu7_1).unwrap();
    let txid = tx.txid();

    let unchanged = tx
        .into_data()
        .map_bundles::<Authorized>(|t| t, |s| s, |o| o);
    let without_transparent = unchanged
        .clone()
        .map_bundles::<Authorized>(|_| None, |s| s, |o| o);
    assert_eq!(unchanged.freeze().unwrap().txid(), txid);
    let error = without_transparent.freeze().unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
    assert!(
        alloc::string::ToString::to_string(&error)
            .contains("bundle type 0 has no effecting bundle"),
        "{error}"
    );
}

#[test]
fn envelope_digests_match_the_typed_digests() {
    for tv in super::vectors::TEST_VECTORS {
        let bytes = hex::decode(tv.tx.as_bytes()).unwrap();
        let envelope = Envelope::read(&bytes[..]).unwrap();
        let tx = Transaction::read(&bytes[..], BranchId::Nu7_1).unwrap();
        assert_eq!(
            envelope.txid(|_| None).unwrap(),
            tx.txid(),
            "{}",
            tv.bundles
        );
        assert_eq!(
            envelope.auth_digest(|_| None).unwrap(),
            tx.auth_commitment(),
            "{}",
            tv.bundles
        );
    }
}

/// An envelope of an unknown epoch, or one without its authorizing data, is identified
/// although it does not decode as a typed transaction.
#[test]
fn envelopes_that_do_not_decode_as_typed_transactions_are_identified() {
    // Only unregistered bundles and a registered delta, in an epoch this library does not
    // know: nothing needs decoding.
    let unknown = BundleId::new(BundleType::new(9), BundleVariant::V0);
    let envelope = Envelope::new(
        crate::transaction::v7::Header {
            consensus_branch_id: 0x1234_5678,
            lock_time: 0,
            expiry_height: 0,
        },
        vec![
            ValuePoolDelta {
                bundle: BundleId::FEE,
                value: core::num::NonZeroI64::new(-1_000).unwrap(),
            },
            ValuePoolDelta {
                bundle: unknown,
                value: core::num::NonZeroI64::new(1_000).unwrap(),
            },
        ],
        vec![BundleData {
            bundle: unknown,
            data: vec![1, 2, 3],
        }],
        vec![BundleData {
            bundle: unknown,
            data: vec![4],
        }],
    )
    .unwrap();
    let supplied = |digest: [u8; 32]| move |id: BundleId| (id == unknown).then_some(digest);
    assert_eq!(
        envelope.txid(supplied([0x77; 32])).unwrap(),
        envelope
            .txid_with_bundle_digests(|_| Ok::<_, core::convert::Infallible>([0x77; 32]))
            .unwrap()
    );
    assert_eq!(
        envelope.auth_digest(supplied([0x88; 32])).unwrap(),
        envelope
            .auth_digest_with_bundle_digests(|_| Ok::<_, core::convert::Infallible>([0x88; 32]))
            .unwrap()
    );

    // The standard vector without its authorizing data keeps its identifier, which does
    // not commit to that data, although the typed layer cannot decode it.
    let bytes = hex::decode(super::vectors::TEST_VECTORS[STANDARD].tx.as_bytes()).unwrap();
    let tx = Transaction::read(&bytes[..], BranchId::Nu7_1).unwrap();
    let (header, deltas, effects, _) = Envelope::read(&bytes[..]).unwrap().into_parts();
    let effects_only = Envelope::new(header, deltas, effects, vec![]).unwrap();
    let mut encoded = Vec::new();
    effects_only.write(&mut encoded).unwrap();
    assert!(Transaction::read(&encoded[..], BranchId::Nu7_1).is_err());
    assert_eq!(effects_only.txid(|_| None).unwrap(), tx.txid());

    // The minimal coinbase vector has no authorizing data to begin with.
    let tv = &super::vectors::TEST_VECTORS[MINIMAL_COINBASE];
    let bytes = hex::decode(tv.tx.as_bytes()).unwrap();
    let envelope = Envelope::read(&bytes[..]).unwrap();
    assert!(envelope.auth_bundles().is_empty());
    assert_eq!(
        hex::encode(envelope.txid(|_| None).unwrap().as_ref()),
        tv.txid
    );
}

#[test]
fn envelope_digests_take_supplied_digests_for_unregistered_bundles() {
    use crate::transaction::{
        TransactionDigest, TxVersion,
        txid::{BlockTxCommitmentDigester, v7_bundle_auth_digests, v7_bundle_effects_digests},
        v7::{DigestError, MapKind},
    };

    let bytes = hex::decode(super::vectors::TEST_VECTORS[STANDARD].tx.as_bytes()).unwrap();
    let tx = Transaction::read(&bytes[..], BranchId::Nu7_1).unwrap();
    let (header, mut deltas, mut effects, mut auths) =
        Envelope::read(&bytes[..]).unwrap().into_parts();
    let unknown = BundleId::new(BundleType::new(9), BundleVariant::new(2));
    deltas.push(ValuePoolDelta {
        bundle: unknown,
        value: core::num::NonZeroI64::new(-1).unwrap(),
    });
    effects.push(BundleData {
        bundle: unknown,
        data: vec![1, 2, 3],
    });
    auths.push(BundleData {
        bundle: unknown,
        data: vec![4],
    });
    let envelope = Envelope::new(header, deltas, effects, auths).unwrap();
    let supplied = |effects: [u8; 32]| move |id: BundleId| (id == unknown).then_some(effects);

    // The registered bundles contribute the digests of the typed transaction, and the
    // unregistered one the supplied digest, in encoding order.
    let lookup = |digests: Vec<(BundleId, [u8; 32])>| {
        move |bundle: &BundleData| {
            digests
                .iter()
                .find(|(id, _)| *id == bundle.bundle)
                .map(|(_, digest)| *digest)
                .ok_or(())
        }
    };
    let mut effect_digests = v7_bundle_effects_digests(&tx.digest(TxIdDigester)).unwrap();
    effect_digests.push((unknown, [0x77; 32]));
    let auth = BlockTxCommitmentDigester;
    let mut auth_digests = v7_bundle_auth_digests(
        auth.digest_transparent(TxVersion::V7, tx.transparent_bundle()),
        auth.digest_sapling(TxVersion::V7, tx.sapling_bundle()),
        auth.digest_orchard(TxVersion::V7, tx.orchard_bundle()),
        auth.digest_ironwood(TxVersion::V7, tx.ironwood_bundle()),
    );
    auth_digests.push((unknown, [0x88; 32]));

    let txid = envelope.txid(supplied([0x77; 32])).unwrap();
    assert_eq!(
        Ok(txid),
        envelope.txid_with_bundle_digests(lookup(effect_digests))
    );
    assert_ne!(txid, tx.txid());
    assert_ne!(txid, envelope.txid(supplied([0x78; 32])).unwrap());
    let auth_digest = envelope.auth_digest(supplied([0x88; 32])).unwrap();
    assert_eq!(
        Ok(auth_digest),
        envelope.auth_digest_with_bundle_digests(lookup(auth_digests))
    );
    assert_ne!(auth_digest, tx.auth_commitment());

    // Without the digest of the unregistered bundle, neither can be computed.
    assert_matches::assert_matches!(
        envelope.txid(|_| None),
        Err(DigestError::MissingDigest(id)) if id == unknown
    );
    assert_matches::assert_matches!(
        envelope.auth_digest(|_| None),
        Err(DigestError::MissingDigest(id)) if id == unknown
    );

    // A registered payload that does not decode cannot be digested. The authorizing
    // digest decodes the effecting payload too, for its counts.
    let (header, deltas, mut effects, auths) = Envelope::read(&bytes[..]).unwrap().into_parts();
    let sapling = position(&effects, BundleType::SAPLING);
    effects[sapling].data.push(0);
    let malformed = Envelope::new(header, deltas, effects, auths).unwrap();
    assert_matches::assert_matches!(
        malformed.txid(supplied([0x77; 32])),
        Err(DigestError::InvalidPayload {
            bundle: BundleId::SAPLING,
            map: MapKind::EffectBundles,
            ..
        })
    );
    assert_matches::assert_matches!(
        malformed.auth_digest(supplied([0x88; 32])),
        Err(DigestError::InvalidPayload {
            bundle: BundleId::SAPLING,
            map: MapKind::EffectBundles,
            ..
        })
    );
}

/// The bundle lists that the encoding and the digests write out by hand each hold the
/// pairs the registry permits in their map, in encoding order.
#[test]
fn hand_written_bundle_lists_follow_the_registry() {
    use crate::transaction::{
        txid::{v7_bundle_auth_digests, v7_bundle_effects_digests},
        v7::{Registration, ShieldedBalances, value_pool_deltas},
    };

    let registered = |permitted: fn(&Registration) -> bool| {
        (0..=255)
            .map(|t| BundleId::new(BundleType::new(t), BundleVariant::V0))
            .filter(|id| id.registration().as_ref().is_some_and(permitted))
            .collect::<Vec<_>>()
    };
    let ids = |entries: Vec<(BundleId, [u8; 32])>| {
        entries.into_iter().map(|(id, _)| id).collect::<Vec<_>>()
    };

    let one = ZatBalance::const_from_i64(1);
    let deltas = ValueDeltas {
        transparent: one,
        coinbase: one,
        fee: one,
    };
    let shielded = ShieldedBalances {
        sapling: one,
        orchard: one,
        ironwood: one,
    };
    assert_eq!(
        value_pool_deltas(&deltas, &shielded)
            .iter()
            .map(|d| d.bundle)
            .collect::<Vec<_>>(),
        // The ZIP 233 bundle is registered but not active, so typed data has no delta
        // for it.
        registered(|r| r.value_pool_delta)
            .into_iter()
            .filter(|id| *id != BundleId::NSM)
            .collect::<Vec<_>>()
    );

    // The standard vector has every effecting bundle but the coinbase bundle.
    let (_, verifying) = verifying_vector(&super::vectors::TEST_VECTORS[STANDARD]);
    let mut txid_parts = verifying.digest(TxIdDigester);
    let digest = txid_parts.header_digest;
    txid_parts.v7_digests.as_mut().unwrap().coinbase_digest = Some(digest);
    assert_eq!(
        ids(v7_bundle_effects_digests(&txid_parts).unwrap()),
        registered(|r| r.effecting)
    );
    assert_eq!(
        ids(v7_bundle_auth_digests(
            Some(digest),
            Some(digest),
            Some(digest),
            Some(digest)
        )),
        registered(|r| r.authorizing)
    );
}

#[test]
fn legacy_writers_reject_v7_before_writing() {
    let wire = hex::decode(super::vectors::TEST_VECTORS[MINIMAL_COINBASE].tx).unwrap();
    let tx = Transaction::read(&wire[..], BranchId::Nu7_1).unwrap();
    let mut encoded = Vec::new();
    tx.write(&mut encoded).unwrap();
    assert_eq!(encoded, wire);

    let mut output = vec![0xaa];
    for result in [
        tx.write_v4(&mut output),
        tx.write_v5(&mut output),
        tx.write_v6(&mut output),
    ] {
        assert_eq!(
            result.unwrap_err().kind(),
            corez::io::ErrorKind::InvalidInput
        );
    }
    assert_eq!(output, [0xaa]);
}

#[test]
fn coinbase_readers_agree_on_payload_boundaries() {
    use crate::transaction::v7::{BundleData, coinbase};

    let payload = |tail: &[u8]| {
        let mut data = vec![0; 20];
        data[0] = 1;
        data.extend_from_slice(tail);
        BundleData {
            bundle: BundleId::COINBASE,
            data,
        }
    };

    for tail in [
        &[][..],
        &[1],
        &[0],
        &[0xfd, 0, 0, 0],
        &[0, 0xfd, 1, 0],
        &[0xfe, 1, 0, 0, 2],
        &[0, 0xfe, 0, 0, 0, 2],
        &[0, 1, 42],
        &[0, 1, 42, 1],
        &[0, 0, 42],
    ] {
        let effect = payload(tail);
        let typed = effect.decode(coinbase::CoinbaseBundle::read).unwrap_err();
        let digest = effect.decode(coinbase::encoded_effects_digest).unwrap_err();
        assert_eq!(typed.kind(), digest.kind(), "tail {tail:?}");
    }

    for count in [0, 1, 252, 253, 256] {
        let mut tail = vec![0];
        zcash_protocol::encoding::CompactSize::write(&mut tail, count).unwrap();
        for code in 0..count {
            tail.extend_from_slice(&[code as u8, 42]);
        }
        if count > 0 {
            tail.extend_from_slice(&[7; 16]);
        }
        let effect = payload(&tail);
        let typed = effect.decode(coinbase::CoinbaseBundle::read).unwrap();
        let digest = effect.decode(coinbase::encoded_effects_digest).unwrap();
        assert_eq!(digest, typed.effects_digest());
        let mut encoded = Vec::new();
        typed.write(&mut encoded).unwrap();
        assert_eq!(encoded, effect.data);
    }
}

#[test]
fn coinbase_digest_precedes_accounting_validation() {
    let bytes = hex::decode(super::vectors::TEST_VECTORS[MINIMAL_COINBASE].tx).unwrap();
    let (header, deltas, mut effects, auth) = Envelope::read(&bytes[..]).unwrap().into_parts();
    let cb = effects
        .iter_mut()
        .find(|b| b.bundle == BundleId::COINBASE)
        .unwrap();
    cb.data[4..12].copy_from_slice(&0u64.to_le_bytes());
    cb.data[12..20].copy_from_slice(&1u64.to_le_bytes());
    let envelope = Envelope::new(header, deltas, effects, auth).unwrap();
    let actual = envelope.txid(|_| None).unwrap();
    let mut wire = Vec::new();
    envelope.write(&mut wire).unwrap();
    assert!(Transaction::read(&wire[..], BranchId::Nu7_1).is_err());
    // Independently computed by the ZIP 248 Python oracle.
    assert_eq!(
        hex::encode(actual.as_ref()),
        "4de2d59b335556944ee6a71f0d1c56dff1be49aa0dae37895ee31082719eb3ce"
    );
    let (header, deltas, mut effects, auth) = envelope.into_parts();
    let cb = effects
        .iter_mut()
        .find(|b| b.bundle == BundleId::COINBASE)
        .unwrap();
    cb.data.pop();
    assert!(
        Envelope::new(header, deltas, effects, auth)
            .unwrap()
            .txid(|_| None)
            .is_err()
    );
}

#[test]
fn typed_expiry_height_boundaries() {
    let bytes = hex::decode(super::vectors::TEST_VECTORS[MINIMAL_COINBASE].tx).unwrap();
    let tx = Transaction::read(&bytes[..], BranchId::Nu7_1).unwrap();
    let (header, deltas, effects, auth) = Envelope::read(&bytes[..]).unwrap().into_parts();
    for (height, accepted) in [(0, true), (499_999_999, true), (500_000_000, false)] {
        let made = TransactionData::<Authorized>::from_parts_v7(
            BranchId::Nu7_1,
            tx.lock_time(),
            height.into(),
            tx.transparent_bundle().cloned(),
            None,
            None,
            None,
            tx.v7_fields().unwrap().clone(),
        );
        assert_eq!(
            made.err(),
            (!accepted).then_some(crate::transaction::v7::BundleRuleError::ExpiryHeightOutOfRange)
        );
        let mut edited = Vec::new();
        let mut header = header;
        header.expiry_height = height;
        Envelope::new(header, deltas.clone(), effects.clone(), auth.clone())
            .unwrap()
            .write(&mut edited)
            .unwrap();
        assert_eq!(
            Transaction::read(&edited[..], BranchId::Nu7_1).is_ok(),
            accepted
        );
    }
}

#[test]
fn v7_is_rejected_outside_nu7_1() {
    let bytes = hex::decode(super::vectors::TEST_VECTORS[MINIMAL_COINBASE].tx.as_bytes()).unwrap();
    let coinbase = Transaction::read(&bytes[..], BranchId::Nu7_1).unwrap();
    let construct = |branch| {
        TransactionData::<Authorized>::from_parts_v7(
            branch,
            coinbase.lock_time(),
            coinbase.expiry_height(),
            coinbase.transparent_bundle().cloned(),
            None,
            None,
            None,
            coinbase.v7_fields().unwrap().clone(),
        )
    };
    assert_eq!(
        construct(BranchId::Nu7).err(),
        Some(crate::transaction::v7::BundleRuleError::UnsupportedBranch(
            BranchId::Nu7
        )),
    );
    let mut written = Vec::new();
    construct(BranchId::Nu7_1)
        .unwrap()
        .freeze()
        .unwrap()
        .write(&mut written)
        .unwrap();
    assert_eq!(written, bytes);
    let (mut header, deltas, effects, auths) = Envelope::read(&bytes[..]).unwrap().into_parts();
    header.consensus_branch_id = BranchId::Nu7.into();
    let mut edited = Vec::new();
    Envelope::new(header, deltas, effects, auths)
        .unwrap()
        .write(&mut edited)
        .unwrap();
    assert!(Transaction::read(&edited[..], BranchId::Nu7).is_err());
}

#[test]
fn prepared_signatures_read_previous_outputs_only_once() {
    let tv = &super::vectors::TEST_VECTORS[STANDARD];
    let (_, tx) = verifying_vector(tv);
    let bundle = tx.transparent_bundle().unwrap();
    let prev = &bundle.authorization;
    assert!(bundle.vin.len() > 1);
    let prepared = crate::transaction::sighash::V7SignatureHashes::new(&tx).unwrap();
    for index in 0..bundle.vin.len() {
        let script = &prev.script_pubkeys[index];
        let input = TransparentSignableInput::from_parts(
            bundle,
            SighashType::ALL,
            index,
            script,
            script,
            prev.amounts[index],
        )
        .unwrap();
        let digest = prepared
            .signature_hash(&SignableInput::Transparent(input))
            .unwrap();
        assert_eq!(hex::encode(digest.as_ref()), tv.sighashes[index].1);
    }
    for pool in [
        ShieldedBundleType::Sapling,
        ShieldedBundleType::Orchard,
        ShieldedBundleType::Ironwood,
    ] {
        prepared.shielded_sighashes(pool).unwrap();
    }
    assert_eq!(
        prev.reads.get(),
        2,
        "each previous-output list is read once"
    );
}

#[test]
fn signature_digests_reject_mismatched_signers() {
    let (_, verifying) = verifying_vector(&super::vectors::TEST_VECTORS[0]);
    let txid_parts = verifying.digest(TxIdDigester);
    let bundle = verifying.transparent_bundle().unwrap();
    let scripts = bundle.authorization.input_scriptpubkeys();
    let amounts = bundle.authorization.input_amounts();
    for hash_type in [
        SighashType::NONE,
        SighashType::SINGLE,
        SighashType::ALL_ANYONECANPAY,
    ] {
        let input = TransparentSignableInput::from_parts(
            bundle,
            hash_type,
            0,
            &scripts[0],
            &scripts[0],
            amounts[0],
        )
        .unwrap();
        assert_eq!(
            signature_hash(&verifying, &SignableInput::Transparent(input), &txid_parts).err(),
            Some(SighashError::UnsupportedHashType(hash_type.encode()))
        );
    }
    assert_eq!(
        signature_hash(&verifying, &SignableInput::Shielded, &txid_parts).err(),
        Some(SighashError::SignerVersionMismatch)
    );
    let actions = verifying.orchard_bundle().unwrap().actions().len();
    assert_eq!(
        signature_hash(
            &verifying,
            &SignableInput::V7Shielded {
                bundle_type: ShieldedBundleType::Orchard,
                signature: ShieldedSignature::SpendAuth { index: actions },
            },
            &txid_parts,
        )
        .err(),
        Some(SighashError::IndexOutOfRange)
    );
    // The shielding vector has no Sapling bundle.
    let (_, shielding) = verifying_vector(&super::vectors::TEST_VECTORS[SHIELDING]);
    assert_eq!(
        signature_hash(
            &shielding,
            &SignableInput::V7Shielded {
                bundle_type: ShieldedBundleType::Sapling,
                signature: ShieldedSignature::Binding,
            },
            &shielding.digest(TxIdDigester),
        )
        .err(),
        Some(SighashError::MissingBundle(ShieldedBundleType::Sapling))
    );

    // A signer whose spent output differs from the authorizing context.
    let input = TransparentSignableInput::from_parts(
        bundle,
        SighashType::ALL,
        0,
        &scripts[0],
        &scripts[0],
        (amounts[0] + Zatoshis::const_from_u64(1)).unwrap(),
    )
    .unwrap();
    assert_eq!(
        signature_hash(&verifying, &SignableInput::Transparent(input), &txid_parts).err(),
        Some(SighashError::SpentOutputMismatch)
    );

    // An authorizing context that does not describe every input.
    let (tx, _) = verifying_vector(&super::vectors::TEST_VECTORS[0]);
    let short = with_spent_outputs(
        &tx,
        SpentOutputs {
            reads: Default::default(),
            amounts: Vec::new(),
            script_pubkeys: Vec::new(),
        },
    );
    assert_eq!(
        signature_hash(
            &short,
            &SignableInput::V7Shielded {
                bundle_type: ShieldedBundleType::Orchard,
                signature: ShieldedSignature::Binding,
            },
            &short.digest(TxIdDigester),
        )
        .err(),
        Some(SighashError::SpentOutputMismatch)
    );

    // Digests without the v7 parts.
    let mut incomplete = txid_parts.clone();
    incomplete.v7_digests = None;
    assert_eq!(
        signature_hash(
            &verifying,
            &SignableInput::V7Shielded {
                bundle_type: ShieldedBundleType::Orchard,
                signature: ShieldedSignature::Binding,
            },
            &incomplete,
        )
        .err(),
        Some(SighashError::MissingV7Digests)
    );
}

#[test]
fn pre_v7_signature_digests_reject_v7_signers() {
    let tx = TransactionData::<Authorized>::from_parts_v6(
        BranchId::Nu7_1,
        0,
        BlockHeight::from_u32(0),
        None,
        None,
        None,
        None,
    );
    let txid_parts = tx.digest(TxIdDigester);
    let tx = TransactionData::<Verifying>::from_parts_v6(
        tx.consensus_branch_id(),
        0,
        tx.expiry_height(),
        None,
        None,
        None,
        None,
    );
    assert_eq!(
        signature_hash(
            &tx,
            &SignableInput::V7Shielded {
                bundle_type: ShieldedBundleType::Orchard,
                signature: ShieldedSignature::Binding,
            },
            &txid_parts,
        )
        .err(),
        Some(SighashError::SignerVersionMismatch)
    );
}

#[test]
fn v7_fee_is_explicit() {
    let no_prevouts = |_: &_| -> Result<_, zcash_protocol::value::BalanceError> {
        panic!("a v7 fee needs no previous outputs")
    };
    for tv in super::vectors::TEST_VECTORS {
        let (tx, _) = verifying_vector(tv);
        let paid = tx.fee_paid(no_prevouts);
        if tx.is_coinbase() {
            // A coinbase transaction collects fees instead of paying them.
            assert_eq!(paid, Ok(Some(Zatoshis::ZERO)));
            continue;
        }
        let fee = Zatoshis::try_from(-tx.v7_fields().unwrap().value_deltas.fee).unwrap();
        assert_eq!(paid, Ok(Some(fee)));
    }
}

#[test]
#[should_panic(expected = "from_parts_v7")]
fn v7_data_needs_its_v7_fields() {
    TransactionData::<Authorized>::from_parts(
        crate::transaction::TxVersion::V7,
        BranchId::Nu7_1,
        0,
        BlockHeight::from_u32(0),
        None,
        None,
        None,
        None,
    );
}

/// Reads the frozen vector at `index` as transaction data.
fn vector_data(index: usize) -> TransactionData<Authorized> {
    let tv = &super::vectors::TEST_VECTORS[index];
    Transaction::read(&hex::decode(tv.tx.as_bytes()).unwrap()[..], BranchId::Nu7_1)
        .unwrap()
        .into_data()
}

fn value_deltas(tx: &mut TransactionData<Authorized>) -> &mut ValueDeltas {
    &mut tx.v7.as_mut().unwrap().value_deltas
}

/// The frozen vectors are shaped like transactions consensus could accept, so they pass
/// every rule that one transaction decides by itself.
#[test]
fn transaction_local_rules_accept_the_vectors() {
    for index in 0..super::vectors::TEST_VECTORS.len() {
        assert_eq!(
            vector_data(index).check_v7_transaction_rules(),
            Ok(()),
            "{}",
            super::vectors::TEST_VECTORS[index].bundles
        );
    }
}

#[test]
fn transaction_local_rules_reject_each_violation() {
    use crate::transaction::v7::TransactionRuleError as E;

    let one = ZatBalance::const_from_i64(1);
    type Edit = Box<dyn Fn(&mut TransactionData<Authorized>)>;
    let cases: Vec<(usize, E, Edit)> = vec![
        (
            STANDARD,
            E::FeePositive,
            Box::new(move |tx| value_deltas(tx).fee = one),
        ),
        (
            RICH_COINBASE,
            E::CoinbaseFeeNegative,
            Box::new(move |tx| value_deltas(tx).fee = -one),
        ),
        // This block has no fees, so the coinbase delta is exactly the subsidy left after
        // the lockbox deposit. One zatoshi more:
        (
            MINIMAL_COINBASE,
            E::CoinbaseDeltaMismatch,
            Box::new(move |tx| {
                let deltas = value_deltas(tx);
                deltas.coinbase = (deltas.coinbase + one).unwrap();
            }),
        ),
        // One zatoshi less:
        (
            MINIMAL_COINBASE,
            E::CoinbaseDeltaMismatch,
            Box::new(move |tx| {
                let deltas = value_deltas(tx);
                deltas.coinbase = (deltas.coinbase - one).unwrap();
            }),
        ),
        (
            MINIMAL_COINBASE,
            E::CoinbaseExpiryMismatch,
            Box::new(|tx| tx.expiry_height = tx.expiry_height + 1),
        ),
        (
            MINIMAL_COINBASE,
            E::TransparentDeltaMismatch,
            Box::new(move |tx| {
                let deltas = value_deltas(tx);
                deltas.transparent = (deltas.transparent + one).unwrap();
            }),
        ),
        // Without its coinbase bundle, the transaction only has outputs: its Sapling
        // bundle has no spends, and its Ironwood bundle has spends disabled.
        (
            RICH_COINBASE,
            E::NoInputs,
            Box::new(|tx| {
                let fields = tx.v7.as_mut().unwrap();
                fields.coinbase_bundle = None;
                fields.value_deltas.coinbase = ZatBalance::zero();
                // Only a coinbase transaction collects fees.
                fields.value_deltas.fee = ZatBalance::zero();
            }),
        ),
        // Only the transparent input is left.
        (
            STANDARD,
            E::NoOutputs,
            Box::new(|tx| {
                tx.transparent_bundle.as_mut().unwrap().vout.clear();
                tx.sapling_bundle = None;
                tx.orchard_bundle = None;
                tx.ironwood_bundle = None;
            }),
        ),
        // With inputs, the spent outputs are worth at least nothing, so the delta cannot
        // be below the negated total of the created outputs.
        (
            STANDARD,
            E::TransparentDeltaMismatch,
            Box::new(move |tx| {
                let outputs: u64 = tx
                    .transparent_bundle
                    .as_ref()
                    .unwrap()
                    .vout
                    .iter()
                    .map(|output| output.value().into_u64())
                    .sum();
                value_deltas(tx).transparent =
                    ZatBalance::from_i64(-i64::try_from(outputs).unwrap() - 1).unwrap();
            }),
        ),
        (
            STANDARD,
            E::Unbalanced,
            Box::new(move |tx| {
                let deltas = value_deltas(tx);
                deltas.fee = (deltas.fee - one).unwrap();
            }),
        ),
    ];
    for (index, expected, edit) in cases {
        let mut tx = vector_data(index);
        edit(&mut tx);
        assert_eq!(tx.check_v7_transaction_rules(), Err(expected));
    }

    // A negative Orchard balance decodes, since the transaction is well-formed.
    let deposit = decode_edited(STANDARD, |deltas, _, _| {
        deltas
            .iter_mut()
            .find(|delta| delta.bundle == BundleId::ORCHARD)
            .unwrap()
            .value = core::num::NonZeroI64::new(-1).unwrap();
    })
    .expect("a negative Orchard balance is well-formed");
    assert_eq!(
        deposit.check_v7_transaction_rules(),
        Err(E::OrchardBalanceNegative)
    );

    // An Orchard bundle with outputs disabled is not an output.
    const SPENDS_ONLY: u8 = 0b01;
    let mut spends_only = decode_edited(STANDARD, |_, effects, _| {
        let orchard = position(effects, BundleType::ORCHARD);
        *effects[orchard].data.last_mut().unwrap() = SPENDS_ONLY;
    })
    .expect("the flags of an Orchard bundle are not checked by decoding");
    spends_only
        .transparent_bundle
        .as_mut()
        .unwrap()
        .vout
        .clear();
    spends_only.sapling_bundle = None;
    spends_only.ironwood_bundle = None;
    assert_eq!(spends_only.check_v7_transaction_rules(), Err(E::NoOutputs));
}

/// Moves `amount` zatoshis of the transparent transaction value pool into the first
/// transparent output of `tx`, or out of it for a negative amount, keeping its
/// transparent delta consistent.
fn pay_more_to_first_output(tx: &mut TransactionData<Authorized>, amount: i64) {
    let deltas = value_deltas(tx);
    deltas.transparent = (deltas.transparent - ZatBalance::from_i64(amount).unwrap()).unwrap();
    let output = &mut tx.transparent_bundle.as_mut().unwrap().vout[0];
    let value = i64::try_from(output.value().into_u64()).unwrap() + amount;
    *output = transparent::TxOut::new(
        Zatoshis::from_nonnegative_i64(value).unwrap(),
        output.script_pubkey().clone(),
    );
}

/// ZIP 235 removes 60% of a block's fees from circulation, rounded down, and the coinbase
/// delta states exactly that contribution.
#[test]
fn coinbase_delta_states_the_exact_zip_235_contribution() {
    use crate::transaction::v7::TransactionRuleError as E;

    let fee = i64::from(vector_data(RICH_COINBASE).v7.unwrap().value_deltas.fee);
    let contribution = |fee: i64| 6 * fee / 10;
    assert!(fee > 0, "the vector collects fees");

    // The miner keeps all the fees: the transaction balances, but contributes nothing.
    let mut keeps_all_fees = vector_data(RICH_COINBASE);
    let kept = contribution(fee);
    let deltas = value_deltas(&mut keeps_all_fees);
    deltas.coinbase = (deltas.coinbase + ZatBalance::from_i64(kept).unwrap()).unwrap();
    pay_more_to_first_output(&mut keeps_all_fees, kept);
    assert_eq!(
        keeps_all_fees.check_v7_transaction_rules(),
        Err(E::CoinbaseDeltaMismatch)
    );

    // Nine more zatoshis of fees raise the contribution by five, since 60% of nine
    // rounds down, and the miner's share by four.
    const MORE_FEES: i64 = 9;
    let more = contribution(fee + MORE_FEES) - contribution(fee);
    assert_eq!(
        fee % 10,
        0,
        "the rounding below assumes a fee that 60% divides"
    );
    assert_eq!(more, 5);
    let mut rounded_down = vector_data(RICH_COINBASE);
    let deltas = value_deltas(&mut rounded_down);
    deltas.fee = (deltas.fee + ZatBalance::from_i64(MORE_FEES).unwrap()).unwrap();
    deltas.coinbase = (deltas.coinbase - ZatBalance::from_i64(more).unwrap()).unwrap();
    pay_more_to_first_output(&mut rounded_down, MORE_FEES - more);
    assert_eq!(rounded_down.check_v7_transaction_rules(), Ok(()));

    // Rounding the contribution up instead is rejected.
    let mut rounded_up = rounded_down.clone();
    let deltas = value_deltas(&mut rounded_up);
    deltas.coinbase = (deltas.coinbase - ZatBalance::const_from_i64(1)).unwrap();
    pay_more_to_first_output(&mut rounded_up, -1);
    assert_eq!(
        rounded_up.check_v7_transaction_rules(),
        Err(E::CoinbaseDeltaMismatch)
    );
}

/// Transactions of earlier versions have none of these rules.
#[test]
fn transaction_local_rules_accept_earlier_versions() {
    let v5 = TransactionData::<Authorized>::from_parts(
        TxVersion::V5,
        BranchId::Nu5,
        0,
        BlockHeight::from_u32(0),
        None,
        None,
        None,
        None,
    );
    assert_eq!(v5.check_v7_transaction_rules(), Ok(()));
}

/// The ZIP 233 bundle is registered for v7 but not active, so a typed transaction cannot
/// have its delta, whatever its sign. The envelope still parses and identifies it.
#[test]
fn typed_decoding_rejects_a_zip_233_delta() {
    for value in [-1, 1] {
        let add_delta = |deltas: &mut Vec<ValuePoolDelta>| {
            deltas.push(ValuePoolDelta {
                bundle: BundleId::NSM,
                value: core::num::NonZeroI64::new(value).unwrap(),
            })
        };
        let error = decode_edited(STANDARD, |deltas, _, _| add_delta(deltas))
            .expect_err("the ZIP 233 bundle is not active");
        assert!(
            alloc::format!("{error}").contains("bundle type 6 is not active"),
            "{error}"
        );

        let bytes = hex::decode(super::vectors::TEST_VECTORS[STANDARD].tx.as_bytes()).unwrap();
        let (header, mut deltas, effects, auths) = Envelope::read(&bytes[..]).unwrap().into_parts();
        add_delta(&mut deltas);
        let envelope = Envelope::new(header, deltas, effects, auths).unwrap();
        envelope.txid(|_| None).unwrap();
    }
}

#[test]
fn shielded_sighashes_match_each_signature_digest() {
    use crate::transaction::sighash::V7SignatureHashes;
    use orchard::bundle::SignatureDigests as _;

    for tv in super::vectors::TEST_VECTORS {
        let (_, verifying) = verifying_vector(tv);
        let prepared = V7SignatureHashes::new(&verifying).unwrap();
        let mut expected = tv
            .sighashes
            .iter()
            .filter(|(label, _)| label.starts_with("s "));
        for (bundle_type, count) in [
            (
                ShieldedBundleType::Sapling,
                verifying
                    .sapling_bundle()
                    .map(|b| b.shielded_spends().len()),
            ),
            (
                ShieldedBundleType::Orchard,
                verifying.orchard_bundle().map(|b| b.actions().len()),
            ),
            (
                ShieldedBundleType::Ironwood,
                verifying.ironwood_bundle().map(|b| b.actions().len()),
            ),
        ] {
            let sighashes = prepared.shielded_sighashes(bundle_type);
            let Some(count) = count else {
                assert_eq!(sighashes, Err(SighashError::MissingBundle(bundle_type)));
                continue;
            };
            let sighashes = sighashes.unwrap();
            let pool = BundleType::from(bundle_type).id();
            for index in 0..count {
                let (label, digest) = expected.next().unwrap();
                assert_eq!(*label, alloc::format!("s {pool} {index}"));
                assert_eq!(hex::encode(sighashes.spend_auth(index).unwrap()), *digest);
            }
            let (label, digest) = expected.next().unwrap();
            assert_eq!(*label, alloc::format!("s {pool} b"));
            assert_eq!(hex::encode(sighashes.binding()), *digest);
            assert_eq!(sighashes.spend_auth(count), None);
        }
        assert!(expected.next().is_none());
    }
}
