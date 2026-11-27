//! Utility functions for computing bundle commitments

use blake2b_simd::{Hash as Blake2bHash, Params, State};

use crate::{
    Action, Anchor, ValuePool,
    bundle::{Authorization, Authorized, Bundle, CommitmentError, TxVersion},
};

const ZCASH_ORCHARD_V5_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdOrchardHash";
const ZCASH_ORCHARD_V6_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdOrchardH_v6";
const ZCASH_ORCHARD_ACTIONS_COMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdOrcActCHash";
const ZCASH_ORCHARD_ACTIONS_MEMOS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdOrcActMHash";
const ZCASH_ORCHARD_ACTIONS_NONCOMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdOrcActNHash";
const ZCASH_ORCHARD_V5_SIGS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthOrchaHash";
const ZCASH_ORCHARD_V6_SIGS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthOrchaH_v6";
const ZCASH_IRONWOOD_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdIronwd_H_v6";
const ZCASH_IRONWOOD_ACTIONS_COMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdIrnActCH_v6";
const ZCASH_IRONWOOD_ACTIONS_MEMOS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdIrnActMH_v6";
const ZCASH_IRONWOOD_ACTIONS_NONCOMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdIrnActNH_v6";
const ZCASH_IRONWOOD_SIGS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthIrnwdH_v6";
const ZCASH_ORCHARD_V7_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdOrchardH_v7";
const ZCASH_ORCHARD_V7_SIGS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthOrchaH_v7";
const ZCASH_IRONWOOD_V7_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdIronwd_Hash";
const ZCASH_IRONWOOD_V7_SIGS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthIrnwdHash";

/// The field encoding of a v7 `sighashInfo` selecting sighash variant 0, which has no
/// associated data: `sizeSighashInfo = 1` followed by `sighashVariant = 0`.
///
/// ZIP 248 defines only variant 0 for the Orchard and Ironwood bundles, so every v7
/// `OrchardSignature` starts with these bytes.
pub const V7_SIGHASH_INFO_V0: [u8; 2] = [0x01, 0x00];

#[derive(Clone, Copy, Debug)]
struct BundleCommitmentPersonalizations {
    bundle: &'static [u8; 16],
    actions_compact: &'static [u8; 16],
    actions_memos: &'static [u8; 16],
    actions_noncompact: &'static [u8; 16],
    auth: &'static [u8; 16],
}

const ORCHARD_V5_PERSONALIZATIONS: BundleCommitmentPersonalizations =
    BundleCommitmentPersonalizations {
        bundle: ZCASH_ORCHARD_V5_HASH_PERSONALIZATION,
        actions_compact: ZCASH_ORCHARD_ACTIONS_COMPACT_HASH_PERSONALIZATION,
        actions_memos: ZCASH_ORCHARD_ACTIONS_MEMOS_HASH_PERSONALIZATION,
        actions_noncompact: ZCASH_ORCHARD_ACTIONS_NONCOMPACT_HASH_PERSONALIZATION,
        auth: ZCASH_ORCHARD_V5_SIGS_HASH_PERSONALIZATION,
    };

// Orchard v6 deliberately reuses the v5 action-level personalizations
// (compact/memos/noncompact); only the top-level `bundle` and `auth` strings gain `_v6`.
// Ironwood instead uses fresh `_v6` strings throughout. Either way the top-level digest is
// domain-separated by its `bundle`/`auth` personalization, so reusing the action-level ones
// cannot collide across formats.
const ORCHARD_V6_PERSONALIZATIONS: BundleCommitmentPersonalizations =
    BundleCommitmentPersonalizations {
        bundle: ZCASH_ORCHARD_V6_HASH_PERSONALIZATION,
        actions_compact: ZCASH_ORCHARD_ACTIONS_COMPACT_HASH_PERSONALIZATION,
        actions_memos: ZCASH_ORCHARD_ACTIONS_MEMOS_HASH_PERSONALIZATION,
        actions_noncompact: ZCASH_ORCHARD_ACTIONS_NONCOMPACT_HASH_PERSONALIZATION,
        auth: ZCASH_ORCHARD_V6_SIGS_HASH_PERSONALIZATION,
    };

// ZIP 248 keeps each pool's v6 action-level personalizations and changes only the
// bundle and authorizing roots, because the v7 roots commit to different data.
const ORCHARD_V7_PERSONALIZATIONS: BundleCommitmentPersonalizations =
    BundleCommitmentPersonalizations {
        bundle: ZCASH_ORCHARD_V7_HASH_PERSONALIZATION,
        auth: ZCASH_ORCHARD_V7_SIGS_HASH_PERSONALIZATION,
        ..ORCHARD_V6_PERSONALIZATIONS
    };

const IRONWOOD_V7_PERSONALIZATIONS: BundleCommitmentPersonalizations =
    BundleCommitmentPersonalizations {
        bundle: ZCASH_IRONWOOD_V7_HASH_PERSONALIZATION,
        auth: ZCASH_IRONWOOD_V7_SIGS_HASH_PERSONALIZATION,
        ..IRONWOOD_V6_PERSONALIZATIONS
    };

const IRONWOOD_V6_PERSONALIZATIONS: BundleCommitmentPersonalizations =
    BundleCommitmentPersonalizations {
        bundle: ZCASH_IRONWOOD_HASH_PERSONALIZATION,
        actions_compact: ZCASH_IRONWOOD_ACTIONS_COMPACT_HASH_PERSONALIZATION,
        actions_memos: ZCASH_IRONWOOD_ACTIONS_MEMOS_HASH_PERSONALIZATION,
        actions_noncompact: ZCASH_IRONWOOD_ACTIONS_NONCOMPACT_HASH_PERSONALIZATION,
        auth: ZCASH_IRONWOOD_SIGS_HASH_PERSONALIZATION,
    };

/// The hash format used to compute a bundle's transaction-ID and authorizing digests,
/// selected from the bundle's pool and the version of the transaction it is encoded in.
/// Orchard bundles use the v5, v6, or v7 format according to the transaction; Ironwood
/// bundles exist only in v6 and v7 transactions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BundleCommitmentFormat {
    OrchardV5,
    OrchardV6,
    IronwoodV6,
    OrchardV7,
    IronwoodV7,
}

impl ValuePool {
    pub(crate) fn commitment_format(
        self,
        tx_version: TxVersion,
    ) -> Result<BundleCommitmentFormat, CommitmentError> {
        match (self, tx_version) {
            (ValuePool::Orchard, TxVersion::V5) => Ok(BundleCommitmentFormat::OrchardV5),
            (ValuePool::Orchard, TxVersion::V6) => Ok(BundleCommitmentFormat::OrchardV6),
            (ValuePool::Ironwood, TxVersion::V5) => Err(CommitmentError::InvalidTransactionVersion),
            (ValuePool::Ironwood, TxVersion::V6) => Ok(BundleCommitmentFormat::IronwoodV6),
            (ValuePool::Orchard, TxVersion::V7) => Ok(BundleCommitmentFormat::OrchardV7),
            (ValuePool::Ironwood, TxVersion::V7) => Ok(BundleCommitmentFormat::IronwoodV7),
        }
    }
}

impl BundleCommitmentFormat {
    fn personalizations(self) -> BundleCommitmentPersonalizations {
        match self {
            BundleCommitmentFormat::OrchardV5 => ORCHARD_V5_PERSONALIZATIONS,
            BundleCommitmentFormat::OrchardV6 => ORCHARD_V6_PERSONALIZATIONS,
            BundleCommitmentFormat::IronwoodV6 => IRONWOOD_V6_PERSONALIZATIONS,
            BundleCommitmentFormat::OrchardV7 => ORCHARD_V7_PERSONALIZATIONS,
            BundleCommitmentFormat::IronwoodV7 => IRONWOOD_V7_PERSONALIZATIONS,
        }
    }

    fn is_v7(self) -> bool {
        matches!(
            self,
            BundleCommitmentFormat::OrchardV7 | BundleCommitmentFormat::IronwoodV7
        )
    }

    pub(crate) fn includes_anchor_in_txid_digest(self) -> bool {
        matches!(self, BundleCommitmentFormat::OrchardV5)
    }

    /// v7 commits to the value balance through the value pool delta map instead.
    fn includes_value_balance_in_txid_digest(self) -> bool {
        !self.is_v7()
    }
}

fn hasher(personal: &[u8; 16]) -> State {
    Params::new().hash_length(32).personal(personal).to_state()
}

/// Write disjoint parts of each bundle action as 3 separate hashes
/// as defined in [ZIP-244: Transaction Identifier Non-Malleability][zip244]:
/// * \[(nullifier, cmx, ephemeral_key, enc_ciphertext\[..52\])*\] personalized
///   with the format's compact-action personalization string
/// * \[enc_ciphertext\[52..564\]*\] (memo ciphertexts) personalized
///   with the format's action-memos personalization string
/// * \[(cv, rk, enc_ciphertext\[564..\], out_ciphertext)*\] personalized
///   with the format's non-compact-action personalization string
///
/// Then, hash these together along with (flags, value_balance_orchard, and — for the v5
/// transaction format only — anchor_orchard), personalized with the format's bundle
/// personalization string. In the v6 format the anchor is included by
/// `hash_bundle_auth_data` instead. The v7 format ([ZIP 248] T.3.3 and T.3.4) commits to
/// the flags only: its value balance is committed by the value pool delta map, and its
/// anchor is authorizing data.
///
/// [ZIP 248]: https://zips.z.cash/zip-0248
///
/// Returns [`CommitmentError::InvalidTransactionVersion`] if `tx_version` is not valid for the
/// bundle's [`BundleVersion`].
///
/// [zip244]: https://zips.z.cash/zip-0244
/// [`BundleVersion`]: crate::bundle::BundleVersion
pub(crate) fn hash_bundle_txid_data<A: Authorization, V: Copy + Into<i64>>(
    bundle: &Bundle<A, V>,
    tx_version: TxVersion,
) -> Result<Blake2bHash, CommitmentError> {
    let format = bundle
        .bundle_version()
        .value_pool()
        .commitment_format(tx_version)?;
    let mut h = hash_actions_and_flags(format, bundle.actions(), bundle.flag_byte());
    if format.includes_value_balance_in_txid_digest() {
        h.update(&(*bundle.value_balance()).into().to_le_bytes());
    }
    if format.includes_anchor_in_txid_digest() {
        h.update(&bundle.anchor().to_bytes());
    }
    Ok(h.finalize())
}

/// [ZIP 248] T.3.3 `orchard_effects_digest` or T.3.4 `ironwood_effects_digest`: the
/// effects digest of a v7 bundle of `value_pool`, from its Actions and its encoded
/// `flagsOrchard` byte.
///
/// This is the digest that [`Bundle::commitment`] computes for a v7 bundle, and it
/// needs neither the bundle's authorization nor its [`BundleVersion`]: it hashes
/// `flag_byte` as given, whether or not that version permits it.
///
/// [ZIP 248]: https://zips.z.cash/zip-0248
/// [`BundleVersion`]: crate::bundle::BundleVersion
pub fn hash_v7_bundle_effects<'a, S: 'a>(
    value_pool: ValuePool,
    actions: impl IntoIterator<Item = &'a Action<S>>,
    flag_byte: u8,
) -> Blake2bHash {
    hash_actions_and_flags(v7_format(value_pool), actions, flag_byte).finalize()
}

fn v7_format(value_pool: ValuePool) -> BundleCommitmentFormat {
    value_pool
        .commitment_format(TxVersion::V7)
        .expect("both value pools have a v7 commitment format")
}

/// Hashes the Actions and flags of a bundle, the part of its effects digest that every
/// format shares.
fn hash_actions_and_flags<'a, S: 'a>(
    format: BundleCommitmentFormat,
    actions: impl IntoIterator<Item = &'a Action<S>>,
    flag_byte: u8,
) -> State {
    let personalizations = format.personalizations();
    let mut h = hasher(personalizations.bundle);
    let mut ch = hasher(personalizations.actions_compact);
    let mut mh = hasher(personalizations.actions_memos);
    let mut nh = hasher(personalizations.actions_noncompact);

    for action in actions {
        ch.update(&action.nullifier().to_bytes());
        ch.update(&action.cmx().to_bytes());
        ch.update(&action.encrypted_note().epk_bytes);
        ch.update(&action.encrypted_note().enc_ciphertext[..52]);

        mh.update(&action.encrypted_note().enc_ciphertext[52..564]);

        nh.update(&action.cv_net().to_bytes());
        nh.update(&<[u8; 32]>::from(action.rk()));
        nh.update(&action.encrypted_note().enc_ciphertext[564..]);
        nh.update(&action.encrypted_note().out_ciphertext);
    }

    h.update(ch.finalize().as_bytes());
    h.update(mh.finalize().as_bytes());
    h.update(nh.finalize().as_bytes());
    h.update(&[flag_byte]);
    h
}

/// Construct the commitment for the absent bundle as defined in
/// [ZIP-244: Transaction Identifier Non-Malleability][zip244]
///
/// Returns [`CommitmentError::InvalidTransactionVersion`] for a v7 transaction, which
/// omits an absent bundle from its digests instead of committing to it.
///
/// [zip244]: https://zips.z.cash/zip-0244
pub fn hash_bundle_txid_empty(
    value_pool: ValuePool,
    tx_version: TxVersion,
) -> Result<Blake2bHash, CommitmentError> {
    Ok(hasher(
        empty_bundle_format(value_pool, tx_version)?
            .personalizations()
            .bundle,
    )
    .finalize())
}

/// The commitment format of an absent bundle, which only transactions before v7 have.
fn empty_bundle_format(
    value_pool: ValuePool,
    tx_version: TxVersion,
) -> Result<BundleCommitmentFormat, CommitmentError> {
    match value_pool.commitment_format(tx_version)? {
        BundleCommitmentFormat::OrchardV7 | BundleCommitmentFormat::IronwoodV7 => {
            Err(CommitmentError::InvalidTransactionVersion)
        }
        format => Ok(format),
    }
}

/// Construct the commitment to the authorizing data of an
/// authorized bundle as defined in [ZIP-244: Transaction
/// Identifier Non-Malleability][zip244]
///
/// [zip244]: https://zips.z.cash/zip-0244
pub(crate) fn hash_bundle_auth_data<V>(
    bundle: &Bundle<Authorized, V>,
    tx_version: TxVersion,
) -> Result<Blake2bHash, CommitmentError> {
    let format = bundle
        .bundle_version()
        .value_pool()
        .commitment_format(tx_version)?;
    if format.is_v7() {
        let v0 = |signature: [u8; 64]| V7SignatureField {
            sighash_info: &V7_SIGHASH_INFO_V0,
            signature,
        };
        return Ok(hash_v7_auth(
            format,
            bundle.anchor(),
            bundle.authorization().proof().as_ref(),
            bundle
                .actions()
                .iter()
                .map(|action| v0(action.authorization().into())),
            v0(bundle.authorization().binding_signature().into()),
        ));
    }
    let mut h = hasher(format.personalizations().auth);
    h.update(bundle.authorization().proof().as_ref());
    for action in bundle.actions().iter() {
        h.update(&<[u8; 64]>::from(action.authorization()));
    }
    h.update(&<[u8; 64]>::from(
        bundle.authorization().binding_signature(),
    ));
    if !matches!(format, BundleCommitmentFormat::OrchardV5) {
        // v6 commits to the anchor after the signatures.
        h.update(&bundle.anchor().to_bytes());
    }
    Ok(h.finalize())
}

/// A v7 `OrchardSignature` field, as the authorizing digest hashes it.
#[derive(Clone, Copy, Debug)]
pub struct V7SignatureField<'a> {
    /// The field encoding of the signature's `sighashInfo`: `sizeSighashInfo`, then
    /// `sighashInfo`. It is [`V7_SIGHASH_INFO_V0`] for sighash variant 0.
    pub sighash_info: &'a [u8],
    /// The encoded signature.
    pub signature: [u8; 64],
}

/// [ZIP 248] A.1.3 `orchard_auth_digest` or A.1.4 `ironwood_auth_digest`: the
/// authorizing digest of a v7 bundle of `value_pool`, from the fields of its authorizing
/// data.
///
/// This is the digest that [`Bundle::authorizing_commitment`] computes for a v7 bundle,
/// whose signatures all use sighash variant 0. It hashes each `sighashInfo` as given, so
/// it also commits to signatures of other variants, and it does not check the proof
/// length.
///
/// [ZIP 248]: https://zips.z.cash/zip-0248
pub fn hash_v7_bundle_auth<'a>(
    value_pool: ValuePool,
    anchor: &Anchor,
    proof: &[u8],
    spend_auth_sigs: impl IntoIterator<Item = V7SignatureField<'a>>,
    binding_sig: V7SignatureField<'a>,
) -> Blake2bHash {
    hash_v7_auth(
        v7_format(value_pool),
        anchor,
        proof,
        spend_auth_sigs,
        binding_sig,
    )
}

/// ZIP 248 A.1.3: the anchor first, then the proof bytes without their length prefix (as
/// in ZIP 244), then each signature in its `OrchardSignature` field encoding, which
/// includes `sighashInfo`.
fn hash_v7_auth<'a>(
    format: BundleCommitmentFormat,
    anchor: &Anchor,
    proof: &[u8],
    spend_auth_sigs: impl IntoIterator<Item = V7SignatureField<'a>>,
    binding_sig: V7SignatureField<'a>,
) -> Blake2bHash {
    let mut h = hasher(format.personalizations().auth);
    h.update(&anchor.to_bytes());
    h.update(proof);
    for field in spend_auth_sigs.into_iter().chain([binding_sig]) {
        h.update(field.sighash_info);
        h.update(&field.signature);
    }
    h.finalize()
}

/// Construct the commitment for an absent bundle as defined in
/// [ZIP-244: Transaction Identifier Non-Malleability][zip244]
///
/// Returns [`CommitmentError::InvalidTransactionVersion`] for a v7 transaction, which
/// omits an absent bundle from its digests instead of committing to it.
///
/// [zip244]: https://zips.z.cash/zip-0244
pub fn hash_bundle_auth_empty(
    value_pool: ValuePool,
    tx_version: TxVersion,
) -> Result<Blake2bHash, CommitmentError> {
    Ok(hasher(
        empty_bundle_format(value_pool, tx_version)?
            .personalizations()
            .auth,
    )
    .finalize())
}
