//! The sighash variant 0 signature digest of [ZIP 248].
//!
//! [ZIP 248]: https://zips.z.cash/zip-0248

use alloc::vec::Vec;

use blake2b_simd::{Hash as Blake2bHash, Params, State};
use corez::io::Write;

use ::transparent::{
    address::Script,
    sighash::{SighashType, TransparentAuthorizingContext},
};
use zcash_protocol::{consensus::BranchId, encoding::Array, value::Zatoshis};

use crate::{
    encoding::StateWrite,
    transaction::{
        Authorization, TransactionData, TxDigests,
        sighash::{SighashError, SignableInput},
        txid::to_hash_v7,
        v7::{BundleId, BundleVariant, ShieldedBundleType, ShieldedSignature, write_bundle_id},
    },
};

/// `signature_digest` personalization.
const SIGHASH_V7_PERSONALIZATION: &[u8; 16] = b"ZcashSigHash_v7_";
/// S.3 `amounts_sig_digest`.
const AMOUNTS_PERSONALIZATION: &[u8; 16] = b"ZTxTrAmountsHash";
/// S.4 `scriptpubkeys_sig_digest`.
const SCRIPTS_PERSONALIZATION: &[u8; 16] = b"ZTxTrScriptsHash";
/// `sighashVariant` of the only variant ZIP 248 defines.
const SIGHASH_VARIANT_0: u8 = 0;

fn hasher(personal: &[u8; 16]) -> StateWrite {
    StateWrite(Params::new().hash_length(32).personal(personal).to_state())
}

/// The part of the variant 0 signature digest that every signature of a transaction
/// shares: S.1 through S.4.
///
/// Each signature digest continues a copy of this hash state with the signature's bundle
/// and context, so the transaction-wide digests are computed once per transaction.
pub(crate) struct SighashPrefix(State);

impl SighashPrefix {
    pub(crate) fn new(
        consensus_branch_id: BranchId,
        txid_parts: &TxDigests<Blake2bHash>,
        spent: &SpentOutputs,
    ) -> Result<Self, SighashError> {
        let txid =
            to_hash_v7(consensus_branch_id, txid_parts).ok_or(SighashError::MissingV7Digests)?;
        let mut h = hasher(SIGHASH_V7_PERSONALIZATION);
        h.write_all(&[SIGHASH_VARIANT_0]).unwrap();
        h.write_all(txid.as_bytes()).unwrap();
        h.write_all(spent.amounts_sig_digest().as_bytes()).unwrap();
        h.write_all(spent.scriptpubkeys_sig_digest().as_bytes())
            .unwrap();
        Ok(Self(h.0))
    }

    /// Completes the digest of a signature in `bundle` with `signature_context` (S.5-S.7).
    pub(crate) fn digest(&self, bundle: BundleId, signature_context: &[u8]) -> Blake2bHash {
        let mut h = StateWrite(self.0.clone());
        write_bundle_id(&mut h, bundle).unwrap();
        h.write_all(signature_context).unwrap();
        h.finalize()
    }
}

/// Computes the variant 0 signature digest of a signature in a v7 transaction.
///
/// Every signature commits to the transaction identifier, to the amounts and script
/// public keys of all transparent inputs, to the bundle that contains it, and to its
/// position in that bundle.
pub(crate) fn v7_signature_hash<
    TA: TransparentAuthorizingContext,
    A: Authorization<TransparentAuth = TA>,
>(
    tx: &TransactionData<A>,
    signable_input: &SignableInput<'_>,
    txid_parts: &TxDigests<Blake2bHash>,
) -> Result<super::sighash::SignatureHash, SighashError> {
    V7SignatureHashes::from_parts(tx, txid_parts)?.signature_hash(signable_input)
}

/// Prepared variant-0 signature hashes for one v7 transaction. Preparation reads
/// the previous outputs from its transparent authorizing context once. The caller
/// must supply the actual spent outputs through that context, in input order.
pub struct V7SignatureHashes<'a, A: Authorization> {
    tx: &'a TransactionData<A>,
    spent: SpentOutputs,
    prefix: SighashPrefix,
}

impl<'a, A: Authorization> V7SignatureHashes<'a, A>
where
    A::TransparentAuth: TransparentAuthorizingContext,
{
    /// Computes the transaction ID and the two spent-output commitments once.
    pub fn new(tx: &'a TransactionData<A>) -> Result<Self, SighashError> {
        if tx.version() != super::TxVersion::V7 {
            return Err(SighashError::SignerVersionMismatch);
        }
        Self::from_parts(tx, &tx.digest(super::TxIdDigester))
    }

    fn from_parts(
        tx: &'a TransactionData<A>,
        txid_parts: &TxDigests<Blake2bHash>,
    ) -> Result<Self, SighashError> {
        let spent = SpentOutputs::of(tx)?;
        let prefix = SighashPrefix::new(tx.consensus_branch_id, txid_parts, &spent)?;
        Ok(Self { tx, spent, prefix })
    }

    /// Computes the digest for a single signer using the prepared commitments.
    pub fn signature_hash(
        &self,
        signable_input: &SignableInput<'_>,
    ) -> Result<super::sighash::SignatureHash, SighashError> {
        let tx = self.tx;
        let spent = &self.spent;
        let (bundle, context) = match signable_input {
            SignableInput::Shielded => return Err(SighashError::SignerVersionMismatch),
            SignableInput::Transparent(input) => {
                // Variant 0 replaces the transparent sighash types: a signature verified
                // with it must use SIGHASH_ALL.
                if *input.hash_type() != SighashType::ALL {
                    return Err(SighashError::UnsupportedHashType(
                        input.hash_type().encode(),
                    ));
                }
                let index = *input.index();
                // The signer's description of the spent output must agree with the one that
                // every signature commits to through S.3 and S.4.
                if spent.amounts.get(index) != Some(input.value())
                    || spent.script_pubkeys.get(index) != Some(*input.script_pubkey())
                {
                    return Err(SighashError::SpentOutputMismatch);
                }
                (
                    BundleId::TRANSPARENT,
                    transparent_context(tx, spent, index)?,
                )
            }
            SignableInput::V7Shielded {
                bundle_type,
                signature,
            } => {
                let count = shielded_signature_count(tx, *bundle_type)?;
                (
                    BundleId::new((*bundle_type).into(), BundleVariant::V0),
                    shielded_context(*signature, count)?,
                )
            }
        };
        Ok(super::sighash::SignatureHash(
            self.prefix.digest(bundle, &context),
        ))
    }
}

/// The amounts and script public keys of the outputs that a transaction's transparent
/// inputs spend, in input order.
pub(crate) struct SpentOutputs {
    amounts: Vec<Zatoshis>,
    script_pubkeys: Vec<Script>,
}

impl SpentOutputs {
    /// Reads the spent outputs from the transaction's authorizing context, which must
    /// describe one output per input.
    pub(crate) fn of<TA: TransparentAuthorizingContext, A: Authorization<TransparentAuth = TA>>(
        tx: &TransactionData<A>,
    ) -> Result<Self, SighashError> {
        let Some(bundle) = &tx.transparent_bundle else {
            return Ok(Self {
                amounts: Vec::new(),
                script_pubkeys: Vec::new(),
            });
        };
        let amounts = bundle.authorization.input_amounts();
        let script_pubkeys = bundle.authorization.input_scriptpubkeys();
        if amounts.len() != bundle.vin.len() || script_pubkeys.len() != bundle.vin.len() {
            return Err(SighashError::SpentOutputMismatch);
        }
        Ok(Self {
            amounts,
            script_pubkeys,
        })
    }

    /// S.3: the amounts of the coins spent by all transparent inputs.
    fn amounts_sig_digest(&self) -> Blake2bHash {
        let mut h = hasher(AMOUNTS_PERSONALIZATION);
        Array::write(&mut h, &self.amounts, |w, amount| {
            w.write_all(&amount.to_i64_le_bytes())
        })
        .unwrap();
        h.finalize()
    }

    /// S.4: the script public keys of the coins spent by all transparent inputs.
    fn scriptpubkeys_sig_digest(&self) -> Blake2bHash {
        let mut h = hasher(SCRIPTS_PERSONALIZATION);
        Array::write(&mut h, &self.script_pubkeys, |w, script| script.write(w)).unwrap();
        h.finalize()
    }
}

/// The number of spend authorization signatures of a v7 shielded bundle.
pub(crate) fn shielded_signature_count<A: Authorization>(
    tx: &TransactionData<A>,
    bundle_type: ShieldedBundleType,
) -> Result<usize, SighashError> {
    match bundle_type {
        ShieldedBundleType::Sapling => tx
            .sapling_bundle
            .as_ref()
            .map(|b| b.shielded_spends().len()),
        ShieldedBundleType::Orchard => tx.orchard_bundle.as_ref().map(|b| b.actions().len()),
        ShieldedBundleType::Ironwood => tx.ironwood_bundle.as_ref().map(|b| b.actions().len()),
    }
    .ok_or(SighashError::MissingBundle(bundle_type))
}

/// S.7 for a shielded signature: the spend's two-byte position, or nothing for the
/// binding signature.
pub(crate) fn shielded_context(
    signature: ShieldedSignature,
    count: usize,
) -> Result<Vec<u8>, SighashError> {
    match signature {
        ShieldedSignature::Binding => Ok(Vec::new()),
        ShieldedSignature::SpendAuth { index } if index < count => Ok(index_bytes(index)?.to_vec()),
        ShieldedSignature::SpendAuth { .. } => Err(SighashError::IndexOutOfRange),
    }
}

/// S.7 for a transparent input: its previous output, value, script public key, sequence
/// number, and position.
fn transparent_context<A: Authorization>(
    tx: &TransactionData<A>,
    spent: &SpentOutputs,
    index: usize,
) -> Result<Vec<u8>, SighashError> {
    let txin = tx
        .transparent_bundle
        .as_ref()
        .and_then(|b| b.vin.get(index))
        .ok_or(SighashError::IndexOutOfRange)?;

    let mut context = Vec::new();
    txin.prevout().write(&mut context).unwrap();
    context
        .write_all(&spent.amounts[index].to_i64_le_bytes())
        .unwrap();
    spent.script_pubkeys[index].write(&mut context).unwrap();
    context.write_all(&txin.sequence().to_le_bytes()).unwrap();
    context.write_all(&index_bytes(index)?).unwrap();
    Ok(context)
}

/// Encodes a signature's position in its bundle as the two-byte little-endian integer
/// of its context.
fn index_bytes(index: usize) -> Result<[u8; 2], SighashError> {
    u16::try_from(index)
        .map(u16::to_le_bytes)
        .map_err(|_| SighashError::IndexOutOfRange)
}
