use crate::encoding::{StateWrite, WriteBytesExt};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::convert::TryFrom;
use corez::io::Write;

use blake2b_simd::{Hash as Blake2bHash, Params};
use ff::PrimeField;

use ::orchard::{
    ValuePool,
    bundle::{self as orchard, TxVersion as OrchardTxVersion},
};
use ::sapling::{
    Nullifier,
    bundle::{GrothProofBytes, OutputDescription, SpendDescription},
    value::ValueCommitment,
};
use ::transparent::{
    address::Script,
    bundle::{self as transparent, TxIn, TxOut},
};
use zcash_protocol::{
    consensus::{BlockHeight, BranchId},
    value::ZatBalance,
};

use super::{
    Authorization, Authorized, TransactionDigest, TransparentDigests, TxDigests, TxId, TxVersion,
    V7TxIdDigests, v7,
};

/// TxId tree root personalization
pub(crate) const ZCASH_TX_PERSONALIZATION_PREFIX: &[u8; 12] = b"ZcashTxHash_";

// TxId level 1 node personalization
pub(crate) const ZCASH_HEADERS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdHeadersHash";
pub(crate) const ZCASH_TRANSPARENT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdTranspaHash";
const ZCASH_SAPLING_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSaplingHash";

// TxId transparent level 2 node personalization
const ZCASH_PREVOUTS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdPrevoutHash";
const ZCASH_SEQUENCE_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSequencHash";
const ZCASH_OUTPUTS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdOutputsHash";

// TxId sapling level 2 node personalization
const ZCASH_SAPLING_SPENDS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSSpendsHash";
const ZCASH_SAPLING_SPENDS_COMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSSpendCHash";
const ZCASH_SAPLING_SPENDS_NONCOMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSSpendNHash";
const ZCASH_SAPLING_SPENDS_V6_NONCOMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSSpendNH_v6";

const ZCASH_SAPLING_OUTPUTS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSOutputHash";
const ZCASH_SAPLING_OUTPUTS_COMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSOutC__Hash";
const ZCASH_SAPLING_OUTPUTS_MEMOS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSOutM__Hash";
const ZCASH_SAPLING_OUTPUTS_NONCOMPACT_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSOutN__Hash";

pub(crate) const ZCASH_AUTH_PERSONALIZATION_PREFIX: &[u8; 12] = b"ZTxAuthHash_";
const ZCASH_TRANSPARENT_SCRIPTS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthTransHash";
const ZCASH_SAPLING_SIGS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthSapliHash";
const ZCASH_SAPLING_V6_SIGS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthSapliH_v6";
const ZCASH_SAPLING_V7_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxIdSaplingH_v7";
const ZCASH_SAPLING_V7_SIGS_HASH_PERSONALIZATION: &[u8; 16] = b"ZTxAuthSapliH_v7";

fn sapling_spends_noncompact_personalization(version: TxVersion) -> &'static [u8; 16] {
    match version {
        TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 | TxVersion::V5 => {
            ZCASH_SAPLING_SPENDS_NONCOMPACT_HASH_PERSONALIZATION
        }
        TxVersion::V6 | TxVersion::V7 => ZCASH_SAPLING_SPENDS_V6_NONCOMPACT_HASH_PERSONALIZATION,
    }
}

fn sapling_auth_personalization(version: TxVersion) -> &'static [u8; 16] {
    match version {
        TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 | TxVersion::V5 => {
            ZCASH_SAPLING_SIGS_HASH_PERSONALIZATION
        }
        TxVersion::V6 => ZCASH_SAPLING_V6_SIGS_HASH_PERSONALIZATION,
        TxVersion::V7 => ZCASH_SAPLING_V7_SIGS_HASH_PERSONALIZATION,
    }
}

/// Whether the v6 Sapling authorizing digest's trailing anchor is present. The v7 digest
/// hashes the authorizing payload instead, which starts with the anchor.
fn sapling_auth_includes_anchor(version: TxVersion) -> bool {
    match version {
        TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 | TxVersion::V5 => false,
        TxVersion::V6 => true,
        TxVersion::V7 => false,
    }
}

/// Selects the `(value pool, orchard tx version)` pair identifying the
/// `BundleCommitmentDomain` used for Orchard-slot commitments in the given
/// transaction version. The value pool here is only used for empty-bundle
/// commitments (which hash no flags); present bundles compute their commitments
/// from the `BundleVersion` each bundle carries.
fn orchard_commitment_domain(version: TxVersion) -> (ValuePool, OrchardTxVersion) {
    match version {
        TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 | TxVersion::V5 => {
            (ValuePool::Orchard, OrchardTxVersion::V5)
        }
        TxVersion::V6 => (ValuePool::Orchard, OrchardTxVersion::V6),
        TxVersion::V7 => (ValuePool::Orchard, OrchardTxVersion::V7),
    }
}

/// Selects the `(value pool, orchard tx version)` pair for Ironwood commitments. Only v6
/// and v7 transactions have an Ironwood bundle; earlier versions commit to none.
fn ironwood_commitment_domain(version: TxVersion) -> (ValuePool, OrchardTxVersion) {
    match version {
        TxVersion::V7 => (ValuePool::Ironwood, OrchardTxVersion::V7),
        _ => (ValuePool::Ironwood, OrchardTxVersion::V6),
    }
}

fn hasher(personal: &[u8; 16]) -> StateWrite {
    StateWrite(Params::new().hash_length(32).personal(personal).to_state())
}

/// Sequentially append the serialized value of each transparent input
/// to a hash personalized by ZCASH_PREVOUTS_HASH_PERSONALIZATION.
/// In the case that no inputs are provided, this produces a default
/// hash from just the personalization string.
pub(crate) fn transparent_prevout_hash<TransparentAuth: transparent::Authorization>(
    vin: &[TxIn<TransparentAuth>],
) -> Blake2bHash {
    let mut h = hasher(ZCASH_PREVOUTS_HASH_PERSONALIZATION);
    for t_in in vin {
        t_in.prevout().write(&mut h).unwrap();
    }
    h.finalize()
}

/// Hash of the little-endian u32 interpretation of the
/// `sequence` values for each TxIn record passed in vin.
pub(crate) fn transparent_sequence_hash<TransparentAuth: transparent::Authorization>(
    vin: &[TxIn<TransparentAuth>],
) -> Blake2bHash {
    let mut h = hasher(ZCASH_SEQUENCE_HASH_PERSONALIZATION);
    for t_in in vin {
        h.write_u32_le(t_in.sequence()).unwrap();
    }
    h.finalize()
}

/// Sequentially append the full serialized value of each transparent output
/// to a hash personalized by ZCASH_OUTPUTS_HASH_PERSONALIZATION.
/// In the case that no outputs are provided, this produces a default
/// hash from just the personalization string.
pub(crate) fn transparent_outputs_hash<T: Borrow<TxOut>>(vout: &[T]) -> Blake2bHash {
    let mut h = hasher(ZCASH_OUTPUTS_HASH_PERSONALIZATION);
    for t_out in vout {
        t_out.borrow().write(&mut h).unwrap();
    }
    h.finalize()
}

/// Implements [ZIP 244 section T.3a](https://zips.z.cash/zip-0244#t-3a-sapling-spends-digest);
/// the v6 variant is specified in [ZIP 229](https://zips.z.cash/zip-0229).
///
/// Write disjoint parts of each Sapling shielded spend to a pair of hashes:
/// * \[nullifier*\] - personalized with ZCASH_SAPLING_SPENDS_COMPACT_HASH_PERSONALIZATION
/// * \[(cv, anchor, rk)*\] for v5 transactions (v4 is not handled here), personalized with
///   ZCASH_SAPLING_SPENDS_NONCOMPACT_HASH_PERSONALIZATION
/// * \[(cv, rk)*\] for v6 transactions, personalized with
///   ZCASH_SAPLING_SPENDS_V6_NONCOMPACT_HASH_PERSONALIZATION
///
/// Then, hash these together personalized by ZCASH_SAPLING_SPENDS_HASH_PERSONALIZATION
pub(crate) fn hash_sapling_spends<A: sapling::bundle::Authorization>(
    version: TxVersion,
    shielded_spends: &[SpendDescription<A>],
) -> Blake2bHash {
    let write_anchor = match version {
        TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 | TxVersion::V5 => true,
        TxVersion::V6 | TxVersion::V7 => false,
    };
    hash_sapling_spend_effects(
        version,
        shielded_spends.iter().map(|spend| SaplingSpendEffects {
            cv: spend.cv(),
            nullifier: spend.nullifier(),
            rk: spend.rk(),
            anchor: write_anchor.then(|| spend.anchor()),
        }),
    )
}

/// The fields of a Sapling Spend that the transaction identifier commits to.
pub(crate) struct SaplingSpendEffects<'a> {
    pub(crate) cv: &'a ValueCommitment,
    pub(crate) nullifier: &'a Nullifier,
    pub(crate) rk: &'a redjubjub::VerificationKey<redjubjub::SpendAuth>,
    /// The anchor, which only transaction versions before v6 commit to here.
    pub(crate) anchor: Option<&'a jubjub::Base>,
}

fn hash_sapling_spend_effects<'a>(
    version: TxVersion,
    shielded_spends: impl IntoIterator<Item = SaplingSpendEffects<'a>>,
) -> Blake2bHash {
    let mut h = hasher(ZCASH_SAPLING_SPENDS_HASH_PERSONALIZATION);
    let mut shielded_spends = shielded_spends.into_iter().peekable();
    if shielded_spends.peek().is_some() {
        let mut ch = hasher(ZCASH_SAPLING_SPENDS_COMPACT_HASH_PERSONALIZATION);
        let mut nh = hasher(sapling_spends_noncompact_personalization(version));
        for s_spend in shielded_spends {
            // we build the hash of nullifiers separately for compact blocks.
            ch.write_all(s_spend.nullifier.as_ref()).unwrap();

            nh.write_all(&s_spend.cv.to_bytes()).unwrap();
            if let Some(anchor) = s_spend.anchor {
                nh.write_all(&anchor.to_repr()).unwrap();
            }
            nh.write_all(&<[u8; 32]>::from(*s_spend.rk)).unwrap();
        }

        let compact_digest = ch.finalize();
        h.write_all(compact_digest.as_bytes()).unwrap();
        let noncompact_digest = nh.finalize();
        h.write_all(noncompact_digest.as_bytes()).unwrap();
    }
    h.finalize()
}

/// Implements [ZIP 244 section T.3b](https://zips.z.cash/zip-0244#t-3b-sapling-outputs-digest)
///
/// Write disjoint parts of each Sapling shielded output as 3 separate hashes:
/// * \[(cmu, epk, enc_ciphertext\[..52\])*\] personalized with ZCASH_SAPLING_OUTPUTS_COMPACT_HASH_PERSONALIZATION
/// * \[enc_ciphertext\[52..564\]*\] (memo ciphertexts) personalized with ZCASH_SAPLING_OUTPUTS_MEMOS_HASH_PERSONALIZATION
/// * \[(cv, enc_ciphertext\[564..\], out_ciphertext, zkproof)*\] personalized with ZCASH_SAPLING_OUTPUTS_NONCOMPACT_HASH_PERSONALIZATION
///
/// Then, hash these together personalized with ZCASH_SAPLING_OUTPUTS_HASH_PERSONALIZATION
pub(crate) fn hash_sapling_outputs<A>(shielded_outputs: &[OutputDescription<A>]) -> Blake2bHash {
    let mut h = hasher(ZCASH_SAPLING_OUTPUTS_HASH_PERSONALIZATION);
    if !shielded_outputs.is_empty() {
        let mut ch = hasher(ZCASH_SAPLING_OUTPUTS_COMPACT_HASH_PERSONALIZATION);
        let mut mh = hasher(ZCASH_SAPLING_OUTPUTS_MEMOS_HASH_PERSONALIZATION);
        let mut nh = hasher(ZCASH_SAPLING_OUTPUTS_NONCOMPACT_HASH_PERSONALIZATION);
        for s_out in shielded_outputs {
            ch.write_all(s_out.cmu().to_bytes().as_ref()).unwrap();
            ch.write_all(s_out.ephemeral_key().as_ref()).unwrap();
            ch.write_all(&s_out.enc_ciphertext()[..52]).unwrap();

            mh.write_all(&s_out.enc_ciphertext()[52..564]).unwrap();

            nh.write_all(&s_out.cv().to_bytes()).unwrap();
            nh.write_all(&s_out.enc_ciphertext()[564..]).unwrap();
            nh.write_all(&s_out.out_ciphertext()[..]).unwrap();
        }

        h.write_all(ch.finalize().as_bytes()).unwrap();
        h.write_all(mh.finalize().as_bytes()).unwrap();
        h.write_all(nh.finalize().as_bytes()).unwrap();
    }
    h.finalize()
}

/// The txid commits to the hash of all transparent outputs. The
/// prevout and sequence_hash components of txid
pub(crate) fn transparent_digests<A: transparent::Authorization>(
    vin: &[TxIn<A>],
    vout: &[TxOut],
) -> TransparentDigests<Blake2bHash> {
    TransparentDigests {
        prevouts_digest: transparent_prevout_hash(vin),
        sequence_digest: transparent_sequence_hash(vin),
        outputs_digest: transparent_outputs_hash(vout),
    }
}

/// [ZIP 248] A.1.0 `transparent_auth_digest`, from the authorizing data of each input of
/// a v7 transparent bundle: the field encoding of its `sighashInfo`, and its `scriptSig`.
///
/// [ZIP 248]: https://zips.z.cash/zip-0248
pub(crate) fn transparent_v7_auth_digest<'a>(
    inputs: impl IntoIterator<Item = (&'a [u8], &'a Script)>,
) -> Blake2bHash {
    let mut h = hasher(ZCASH_TRANSPARENT_SCRIPTS_HASH_PERSONALIZATION);
    for (sighash_info, script_sig) in inputs {
        h.write_all(sighash_info).unwrap();
        script_sig.write(&mut h).unwrap();
    }
    h.finalize()
}

/// Implements [ZIP 244 section T.1](https://zips.z.cash/zip-0244#t-1-header-digest)
fn hash_header_txid_data(
    version: TxVersion,
    // we commit to the consensus branch ID with the header
    consensus_branch_id: BranchId,
    lock_time: u32,
    expiry_height: BlockHeight,
) -> Blake2bHash {
    let mut h = hasher(ZCASH_HEADERS_HASH_PERSONALIZATION);

    h.write_u32_le(version.header()).unwrap();
    h.write_u32_le(version.version_group_id()).unwrap();
    h.write_u32_le(consensus_branch_id.into()).unwrap();
    h.write_u32_le(lock_time).unwrap();
    h.write_u32_le(expiry_height.into()).unwrap();

    h.finalize()
}

/// Implements [ZIP 244 section T.2](https://zips.z.cash/zip-0244#t-2-transparent-digest)
pub(crate) fn hash_transparent_txid_data(
    t_digests: Option<&TransparentDigests<Blake2bHash>>,
) -> Blake2bHash {
    let mut h = hasher(ZCASH_TRANSPARENT_HASH_PERSONALIZATION);
    if let Some(d) = t_digests {
        h.write_all(d.prevouts_digest.as_bytes()).unwrap();
        h.write_all(d.sequence_digest.as_bytes()).unwrap();
        h.write_all(d.outputs_digest.as_bytes()).unwrap();
    }
    h.finalize()
}

/// Implements [ZIP 244 section T.3](https://zips.z.cash/zip-0244#t-3-sapling-digest);
/// for v6 transactions the Sapling digest follows
/// [ZIP 229](https://zips.z.cash/zip-0229), and for v7 transactions it is the
/// `sapling_effects_digest` of [ZIP 248](https://zips.z.cash/zip-0248), which commits to
/// the value balance through the value pool delta map instead.
fn hash_sapling_txid_data<A: sapling::bundle::Authorization>(
    version: TxVersion,
    bundle: &sapling::Bundle<A, ZatBalance>,
) -> Blake2bHash {
    if version == TxVersion::V7 {
        return sapling_v7_effects_digest(
            bundle
                .shielded_spends()
                .iter()
                .map(|spend| SaplingSpendEffects {
                    cv: spend.cv(),
                    nullifier: spend.nullifier(),
                    rk: spend.rk(),
                    anchor: None,
                }),
            bundle.shielded_outputs(),
        );
    }
    let mut h = hasher(ZCASH_SAPLING_HASH_PERSONALIZATION);
    if !(bundle.shielded_spends().is_empty() && bundle.shielded_outputs().is_empty()) {
        h.write_all(hash_sapling_spends(version, bundle.shielded_spends()).as_bytes())
            .unwrap();

        h.write_all(hash_sapling_outputs(bundle.shielded_outputs()).as_bytes())
            .unwrap();

        h.write_all(&bundle.value_balance().to_i64_le_bytes())
            .unwrap();
    }
    h.finalize()
}

/// [ZIP 248] T.3.2 `sapling_effects_digest`, from the effecting data of a v7 Sapling
/// bundle. The spends carry no anchor, which v7 places in the authorizing data.
///
/// [ZIP 248]: https://zips.z.cash/zip-0248
pub(crate) fn sapling_v7_effects_digest<'a, P>(
    spends: impl IntoIterator<Item = SaplingSpendEffects<'a>>,
    outputs: &[OutputDescription<P>],
) -> Blake2bHash {
    let mut h = hasher(ZCASH_SAPLING_V7_HASH_PERSONALIZATION);
    h.write_all(hash_sapling_spend_effects(TxVersion::V7, spends).as_bytes())
        .unwrap();
    h.write_all(hash_sapling_outputs(outputs).as_bytes())
        .unwrap();
    h.finalize()
}

/// [ZIP 248] A.1.2 `sapling_auth_digest`, from the fields of the authorizing data of a v7
/// Sapling bundle. Each signature is given with the field encoding of its `sighashInfo`.
///
/// [ZIP 248]: https://zips.z.cash/zip-0248
pub(crate) fn sapling_v7_auth_digest<'a>(
    anchor: Option<&jubjub::Base>,
    spend_proofs: impl IntoIterator<Item = &'a GrothProofBytes>,
    spend_auth_sigs: impl IntoIterator<Item = (&'a [u8], [u8; 64])>,
    output_proofs: impl IntoIterator<Item = &'a GrothProofBytes>,
    binding_sig: (&[u8], [u8; 64]),
) -> Blake2bHash {
    let mut h = hasher(ZCASH_SAPLING_V7_SIGS_HASH_PERSONALIZATION);
    if let Some(anchor) = anchor {
        h.write_all(&anchor.to_repr()).unwrap();
    }
    for proof in spend_proofs {
        h.write_all(proof).unwrap();
    }
    for (sighash_info, signature) in spend_auth_sigs {
        h.write_all(sighash_info).unwrap();
        h.write_all(&signature).unwrap();
    }
    for proof in output_proofs {
        h.write_all(proof).unwrap();
    }
    h.write_all(binding_sig.0).unwrap();
    h.write_all(&binding_sig.1).unwrap();
    h.finalize()
}

fn hash_sapling_txid_empty() -> Blake2bHash {
    hasher(ZCASH_SAPLING_HASH_PERSONALIZATION).finalize()
}

/// A TransactionDigest implementation that commits to all of the effecting
/// data of a transaction to produce a nonmalleable transaction identifier.
///
/// This expects and relies upon the existence of canonical encodings for
/// each effecting component of a transaction.
///
/// This implements the [TxId Digest section of ZIP 244](https://zips.z.cash/zip-0244#txid-digest)
pub struct TxIdDigester;

impl<A: Authorization> TransactionDigest<A> for TxIdDigester {
    type HeaderDigest = Blake2bHash;
    type TransparentDigest = Option<TransparentDigests<Blake2bHash>>;
    type SaplingDigest = Option<Blake2bHash>;
    type OrchardDigest = Option<Blake2bHash>;
    type IronwoodDigest = Option<Blake2bHash>;
    type V7Digest = V7TxIdDigests<Blake2bHash>;

    type Digest = TxDigests<Blake2bHash>;

    fn digest_header(
        &self,
        version: TxVersion,
        consensus_branch_id: BranchId,
        lock_time: u32,
        expiry_height: BlockHeight,
    ) -> Self::HeaderDigest {
        hash_header_txid_data(version, consensus_branch_id, lock_time, expiry_height)
    }

    fn digest_transparent(
        &self,
        version: TxVersion,
        transparent_bundle: Option<&transparent::Bundle<A::TransparentAuth>>,
    ) -> Self::TransparentDigest {
        transparent_bundle
            .filter(|b| version != TxVersion::V7 || v7::transparent::has_effects(b))
            .map(|b| transparent_digests(&b.vin, &b.vout))
    }

    fn digest_sapling(
        &self,
        version: TxVersion,
        sapling_bundle: Option<&sapling::Bundle<A::SaplingAuth, ZatBalance>>,
    ) -> Self::SaplingDigest {
        sapling_bundle.map(|bundle| hash_sapling_txid_data(version, bundle))
    }

    fn digest_orchard(
        &self,
        version: TxVersion,
        orchard_bundle: Option<&orchard::Bundle<A::OrchardAuth, ZatBalance>>,
    ) -> Self::OrchardDigest {
        orchard_bundle.map(|b| {
            let (_, tx_version) = orchard_commitment_domain(version);
            b.commitment(tx_version)
                .expect("Orchard bundle flags must be representable in their transaction format")
                .0
        })
    }

    fn digest_ironwood(
        &self,
        version: TxVersion,
        ironwood_bundle: Option<&orchard::Bundle<A::OrchardAuth, ZatBalance>>,
    ) -> Self::IronwoodDigest {
        ironwood_bundle.map(|b| {
            let (_, tx_version) = ironwood_commitment_domain(version);
            b.commitment(tx_version)
                .expect("Ironwood bundle flags must be representable")
                .0
        })
    }

    fn digest_v7(
        &self,
        value_pool_deltas: &[v7::ValuePoolDelta],
        coinbase_bundle: Option<&v7::CoinbaseBundle>,
    ) -> Self::V7Digest {
        V7TxIdDigests {
            value_pool_deltas_digest: v7::digest::value_pool_deltas_digest(value_pool_deltas),
            coinbase_digest: coinbase_bundle.map(v7::CoinbaseBundle::effects_digest),
        }
    }

    fn combine(
        &self,
        header_digest: Self::HeaderDigest,
        transparent_digests: Self::TransparentDigest,
        sapling_digest: Self::SaplingDigest,
        orchard_digest: Self::OrchardDigest,
        ironwood_digest: Self::IronwoodDigest,
        v7_digests: Option<Self::V7Digest>,
    ) -> Self::Digest {
        TxDigests {
            header_digest,
            transparent_digests,
            sapling_digest,
            orchard_digest,
            ironwood_digest,
            v7_digests,
        }
    }
}

pub(crate) fn to_hash(
    _txversion: TxVersion,
    consensus_branch_id: BranchId,
    header_digest: Blake2bHash,
    transparent_digest: Blake2bHash,
    sapling_digest: Option<Blake2bHash>,
    orchard_digest: Option<Blake2bHash>,
) -> Blake2bHash {
    let mut personal = [0; 16];
    personal[..12].copy_from_slice(ZCASH_TX_PERSONALIZATION_PREFIX);
    (&mut personal[12..])
        .write_u32_le(consensus_branch_id.into())
        .unwrap();

    let mut h = hasher(&personal);
    h.write_all(header_digest.as_bytes()).unwrap();
    h.write_all(transparent_digest.as_bytes()).unwrap();
    h.write_all(
        sapling_digest
            .unwrap_or_else(hash_sapling_txid_empty)
            .as_bytes(),
    )
    .unwrap();
    h.write_all(
        orchard_digest
            .unwrap_or_else(|| {
                let (value_pool, tx_version) = orchard_commitment_domain(_txversion);
                orchard::commitments::hash_bundle_txid_empty(value_pool, tx_version)
                    .expect("empty Orchard bundle txid commitment is valid for its tx format")
            })
            .as_bytes(),
    )
    .unwrap();

    h.finalize()
}

pub(crate) fn to_hash_v6(
    consensus_branch_id: BranchId,
    header_digest: Blake2bHash,
    transparent_digest: Blake2bHash,
    sapling_digest: Option<Blake2bHash>,
    orchard_digest: Option<Blake2bHash>,
    ironwood_digest: Option<Blake2bHash>,
) -> Blake2bHash {
    let mut personal = [0; 16];
    personal[..12].copy_from_slice(ZCASH_TX_PERSONALIZATION_PREFIX);
    (&mut personal[12..])
        .write_u32_le(consensus_branch_id.into())
        .unwrap();

    let mut h = hasher(&personal);
    h.write_all(header_digest.as_bytes()).unwrap();
    h.write_all(transparent_digest.as_bytes()).unwrap();
    h.write_all(
        sapling_digest
            .unwrap_or_else(hash_sapling_txid_empty)
            .as_bytes(),
    )
    .unwrap();
    h.write_all(
        orchard_digest
            .unwrap_or_else(|| {
                let (value_pool, tx_version) = orchard_commitment_domain(TxVersion::V6);
                orchard::commitments::hash_bundle_txid_empty(value_pool, tx_version)
                    .expect("empty Orchard bundle txid commitment is valid for its tx format")
            })
            .as_bytes(),
    )
    .unwrap();
    h.write_all(
        ironwood_digest
            .unwrap_or_else(|| {
                let (value_pool, tx_version) = ironwood_commitment_domain(TxVersion::V6);
                orchard::commitments::hash_bundle_txid_empty(value_pool, tx_version)
                    .expect("empty Ironwood bundle txid commitment is valid")
            })
            .as_bytes(),
    )
    .unwrap();

    h.finalize()
}

/// Combines transaction component digests into a transaction ID.
///
/// # Panics
///
/// Panics if `txversion` is v7 and `digests` lacks the v7 digests, which
/// [`TxIdDigester`] computes for every v7 transaction.
///
/// Version 6 transactions include the Ironwood bundle digest as a separate
/// Orchard-shaped digest using Ironwood personalization. If any shielded bundle digest is
/// absent, this substitutes the protocol-defined empty bundle digest for that pool.
pub fn to_txid(
    txversion: TxVersion,
    consensus_branch_id: BranchId,
    digests: &TxDigests<Blake2bHash>,
) -> TxId {
    let txid_digest = if txversion == TxVersion::V7 {
        to_hash_v7(consensus_branch_id, digests)
            .expect("TxIdDigester computes the v7 digests of every v7 transaction")
    } else if txversion.has_ironwood() {
        to_hash_v6(
            consensus_branch_id,
            digests.header_digest,
            hash_transparent_txid_data(digests.transparent_digests.as_ref()),
            digests.sapling_digest,
            digests.orchard_digest,
            digests.ironwood_digest,
        )
    } else {
        to_hash(
            txversion,
            consensus_branch_id,
            digests.header_digest,
            hash_transparent_txid_data(digests.transparent_digests.as_ref()),
            digests.sapling_digest,
            digests.orchard_digest,
        )
    };

    TxId::from_bytes(<[u8; 32]>::try_from(txid_digest.as_bytes()).unwrap())
}

/// Combines the digests of a v7 transaction into its `txid_digest` ([ZIP 248]), or
/// returns `None` if `digests` lacks the v7 digests, which [`TxIdDigester`] computes for
/// every v7 transaction.
///
/// [ZIP 248]: https://zips.z.cash/zip-0248
pub(crate) fn to_hash_v7(
    consensus_branch_id: BranchId,
    digests: &TxDigests<Blake2bHash>,
) -> Option<Blake2bHash> {
    Some(v7::digest::txid_digest(
        consensus_branch_id.into(),
        digests.header_digest,
        digests.v7_digests.as_ref()?.value_pool_deltas_digest,
        v7::digest::effects_bundles_digest(v7_bundle_effects_digests(digests)?),
    ))
}

/// Returns the `bundle_effects_digest` of each bundle in `mEffectBundles` of a v7
/// transaction, in encoding order, or `None` if `digests` lacks the v7 digests.
pub(crate) fn v7_bundle_effects_digests(
    digests: &TxDigests<Blake2bHash>,
) -> Option<Vec<(v7::BundleId, [u8; 32])>> {
    let v7_digests = digests.v7_digests.as_ref()?;
    Some(present_bundles([
        (
            v7::BundleId::TRANSPARENT,
            digests
                .transparent_digests
                .as_ref()
                .map(|d| hash_transparent_txid_data(Some(d))),
        ),
        (v7::BundleId::COINBASE, v7_digests.coinbase_digest),
        (v7::BundleId::SAPLING, digests.sapling_digest),
        (v7::BundleId::ORCHARD, digests.orchard_digest),
        (v7::BundleId::IRONWOOD, digests.ironwood_digest),
    ]))
}

/// Returns the `bundle_auth_digest` of each bundle in `mAuthBundles` of a v7 transaction,
/// in encoding order, from the bundle digests of [`BlockTxCommitmentDigester`].
pub(crate) fn v7_bundle_auth_digests(
    transparent: Option<Blake2bHash>,
    sapling: Option<Blake2bHash>,
    orchard: Option<Blake2bHash>,
    ironwood: Option<Blake2bHash>,
) -> Vec<(v7::BundleId, [u8; 32])> {
    present_bundles([
        (v7::BundleId::TRANSPARENT, transparent),
        (v7::BundleId::SAPLING, sapling),
        (v7::BundleId::ORCHARD, orchard),
        (v7::BundleId::IRONWOOD, ironwood),
    ])
}

/// Keeps the bundles that are present, which contribute their digests in this order.
fn present_bundles<const N: usize>(
    digests: [(v7::BundleId, Option<Blake2bHash>); N],
) -> Vec<(v7::BundleId, [u8; 32])> {
    digests
        .into_iter()
        .filter_map(|(id, digest)| digest.map(|d| (id, bytes32(&d))))
        .collect()
}

pub(crate) fn bytes32(digest: &Blake2bHash) -> [u8; 32] {
    digest
        .as_bytes()
        .try_into()
        .expect("transaction digests are 32 bytes long")
}

/// Digester which constructs a digest of only the witness data.
/// This does not internally commit to the txid, so if that is
/// desired it should be done using the result of this digest
/// function.
pub struct BlockTxCommitmentDigester;

impl TransactionDigest<Authorized> for BlockTxCommitmentDigester {
    /// We use the header digest to pass the transaction version and consensus
    /// branch ID into where they need to be used for personalization string
    /// construction.
    type HeaderDigest = (TxVersion, BranchId);
    /// Each bundle digest is `None` when the bundle has no authorizing data. Before v7,
    /// the commitment substitutes the empty digest of that bundle; v7 omits the bundle.
    type TransparentDigest = Option<Blake2bHash>;
    type SaplingDigest = Option<Blake2bHash>;
    type OrchardDigest = Option<Blake2bHash>;
    type IronwoodDigest = Option<Blake2bHash>;
    type V7Digest = ();

    type Digest = Blake2bHash;

    fn digest_header(
        &self,
        version: TxVersion,
        consensus_branch_id: BranchId,
        _lock_time: u32,
        _expiry_height: BlockHeight,
    ) -> Self::HeaderDigest {
        (version, consensus_branch_id)
    }

    fn digest_transparent(
        &self,
        version: TxVersion,
        transparent_bundle: Option<&transparent::Bundle<transparent::Authorized>>,
    ) -> Self::TransparentDigest {
        let bundle = transparent_bundle?;
        if version == TxVersion::V7 {
            return v7::transparent::has_auth(bundle).then(|| {
                transparent_v7_auth_digest(
                    bundle
                        .vin
                        .iter()
                        .map(|txin| (&v7::SIGHASH_INFO_V0[..], txin.script_sig())),
                )
            });
        }
        let mut h = hasher(ZCASH_TRANSPARENT_SCRIPTS_HASH_PERSONALIZATION);
        for txin in &bundle.vin {
            txin.script_sig().write(&mut h).unwrap();
        }
        Some(h.finalize())
    }

    fn digest_sapling(
        &self,
        version: TxVersion,
        sapling_bundle: Option<&sapling::Bundle<sapling::bundle::Authorized, ZatBalance>>,
    ) -> Self::SaplingDigest {
        let bundle = sapling_bundle?;
        if version == TxVersion::V7 {
            let v0 = |signature: [u8; 64]| (&v7::SIGHASH_INFO_V0[..], signature);
            return Some(sapling_v7_auth_digest(
                bundle.shielded_spends().first().map(|spend| spend.anchor()),
                bundle.shielded_spends().iter().map(|spend| spend.zkproof()),
                bundle
                    .shielded_spends()
                    .iter()
                    .map(|spend| v0((*spend.spend_auth_sig()).into())),
                bundle
                    .shielded_outputs()
                    .iter()
                    .map(|output| output.zkproof()),
                v0(bundle.authorization().binding_sig.into()),
            ));
        }
        let mut h = hasher(sapling_auth_personalization(version));

        for spend in bundle.shielded_spends() {
            h.write_all(spend.zkproof()).unwrap();
        }

        for spend in bundle.shielded_spends() {
            h.write_all(&<[u8; 64]>::from(*spend.spend_auth_sig()))
                .unwrap();
        }

        for output in bundle.shielded_outputs() {
            h.write_all(output.zkproof()).unwrap();
        }

        h.write_all(&<[u8; 64]>::from(bundle.authorization().binding_sig))
            .unwrap();

        if sapling_auth_includes_anchor(version) && !bundle.shielded_spends().is_empty() {
            h.write_all(bundle.shielded_spends()[0].anchor().to_repr().as_ref())
                .unwrap();
        }
        Some(h.finalize())
    }

    fn digest_orchard(
        &self,
        version: TxVersion,
        orchard_bundle: Option<&orchard::Bundle<orchard::Authorized, ZatBalance>>,
    ) -> Self::OrchardDigest {
        let (_, tx_version) = orchard_commitment_domain(version);
        orchard_bundle.map(|b| {
            b.authorizing_commitment(tx_version)
                .expect("Orchard bundle flags must be representable in their tx format")
                .0
        })
    }

    fn digest_ironwood(
        &self,
        version: TxVersion,
        ironwood_bundle: Option<&orchard::Bundle<orchard::Authorized, ZatBalance>>,
    ) -> Self::IronwoodDigest {
        let (_, tx_version) = ironwood_commitment_domain(version);
        ironwood_bundle.map(|b| {
            b.authorizing_commitment(tx_version)
                .expect("Ironwood bundle flags must be representable")
                .0
        })
    }

    fn digest_v7(
        &self,
        _value_pool_deltas: &[v7::ValuePoolDelta],
        _coinbase_bundle: Option<&v7::CoinbaseBundle>,
    ) -> Self::V7Digest {
        // The coinbase bundle has no authorizing data, and the deltas are effects.
    }

    fn combine(
        &self,
        tx_context: Self::HeaderDigest,
        transparent_digest: Self::TransparentDigest,
        sapling_digest: Self::SaplingDigest,
        orchard_digest: Self::OrchardDigest,
        ironwood_digest: Self::IronwoodDigest,
        _v7_digests: Option<Self::V7Digest>,
    ) -> Self::Digest {
        let (txversion, consensus_branch_id) = tx_context;
        if txversion == TxVersion::V7 {
            return v7::digest::auth_digest(
                consensus_branch_id.into(),
                v7::digest::auth_bundles_digest(v7_bundle_auth_digests(
                    transparent_digest,
                    sapling_digest,
                    orchard_digest,
                    ironwood_digest,
                )),
            );
        }

        let mut personal = [0; 16];
        personal[..12].copy_from_slice(ZCASH_AUTH_PERSONALIZATION_PREFIX);
        (&mut personal[12..])
            .write_u32_le(consensus_branch_id.into())
            .unwrap();

        let (orchard_pool, orchard_version) = orchard_commitment_domain(txversion);
        let mut h = hasher(&personal);
        h.write_all(
            transparent_digest
                .unwrap_or_else(|| {
                    hasher(ZCASH_TRANSPARENT_SCRIPTS_HASH_PERSONALIZATION).finalize()
                })
                .as_bytes(),
        )
        .unwrap();
        h.write_all(
            sapling_digest
                .unwrap_or_else(|| hasher(sapling_auth_personalization(txversion)).finalize())
                .as_bytes(),
        )
        .unwrap();
        h.write_all(
            orchard_digest
                .unwrap_or_else(|| {
                    orchard::commitments::hash_bundle_auth_empty(orchard_pool, orchard_version)
                        .expect("empty Orchard bundle auth commitment is valid for its tx format")
                })
                .as_bytes(),
        )
        .unwrap();

        if txversion.has_ironwood() {
            let (ironwood_pool, ironwood_version) = ironwood_commitment_domain(txversion);
            h.write_all(
                ironwood_digest
                    .unwrap_or_else(|| {
                        orchard::commitments::hash_bundle_auth_empty(
                            ironwood_pool,
                            ironwood_version,
                        )
                        .expect("empty Ironwood bundle auth commitment is valid")
                    })
                    .as_bytes(),
            )
            .unwrap();
        }

        h.finalize()
    }
}
