//! Conversion between a v7 [`TransactionData`] and its [`Envelope`].
//!
//! [`TransactionData`] represents the bundles ZIP 248 registers. Decoding rejects a
//! transaction it cannot represent: one with an unregistered pair, an entry in a map
//! the registry forbids for that pair, a registered bundle that its consensus branch is
//! assumed not to activate (the ZIP 233 bundle), a bundle without the authorizing data it
//! needs, or a signature that does not use sighash variant 0. Such a transaction can
//! still be parsed with [`Envelope::read`], and identified with [`Envelope::txid`].
//!
//! Decoding also enforces the other ZIP 248 bundle-local rules: those on each bundle's own
//! fields, such as the coinbase bundle's, and those [`TransactionData::from_parts_v7`]
//! checks, such as that a value pool delta has its effecting bundle. The exception is the
//! rule that transparent signatures use `SIGHASH_ALL`, which only script verification
//! under `zcash_script`'s `Flags::SigHashAllOnly` can check. Decoding leaves the rules
//! that relate bundles to each other's values or to the chain to full validators: for
//! example, that the deltas balance, and the sign of the fee.
//! [`TransactionData::check_v7_transaction_rules`] checks those of them that need only
//! the transaction.

use alloc::vec::Vec;
use corez::io::{self, Read, Write};

use zcash_protocol::{
    consensus::{BlockHeight, BranchId},
    value::ZatBalance,
};

use super::{
    coinbase::CoinbaseBundle,
    envelope::{BundleData, Envelope, Header},
    fields::{ShieldedBalances, V7Fields, ValueDeltas, value_pool_deltas},
    registry::{BundleId, BundleType, Registration},
    rules::BundleRuleError,
    transparent,
};
use crate::transaction::{
    Authorized, TransactionData, TxVersion,
    components::{orchard as orchard_serialization, sapling as sapling_serialization},
};

/// Reads a v7 transaction whose `header` and `nVersionGroupId` fields have already been
/// read.
pub(crate) fn read<R: Read>(reader: R) -> io::Result<TransactionData<Authorized>> {
    from_envelope(Envelope::read_after_version(reader)?)
}

/// Writes a v7 transaction.
pub(crate) fn write<W: Write>(tx: &TransactionData<Authorized>, writer: W) -> io::Result<()> {
    to_envelope(tx)?.write(writer)
}

fn from_envelope(envelope: Envelope) -> io::Result<TransactionData<Authorized>> {
    let header = *envelope.header();
    let consensus_branch_id = BranchId::try_from(header.consensus_branch_id)
        .map_err(|_| invalid("unknown consensus branch ID"))?;
    if !TxVersion::V7.valid_in_branch(consensus_branch_id) {
        return Err(invalid(
            "v7 transactions are not valid in this consensus branch",
        ));
    }

    let (_, deltas, effects, auths) = envelope.into_parts();
    let mut value_deltas = ValueDeltas::default();
    let mut shielded = ShieldedBalances::default();
    for delta in &deltas {
        check_registered(delta.bundle, |r| r.value_pool_delta)?;
        let value = ZatBalance::from_i64(delta.value.get())
            .map_err(|_| invalid("value pool delta is out of range"))?;
        *match delta.bundle {
            BundleId::TRANSPARENT => &mut value_deltas.transparent,
            BundleId::COINBASE => &mut value_deltas.coinbase,
            BundleId::SAPLING => &mut shielded.sapling,
            BundleId::ORCHARD => &mut shielded.orchard,
            BundleId::IRONWOOD => &mut shielded.ironwood,
            BundleId::FEE => &mut value_deltas.fee,
            // ZIP 233 registers this bundle, but NU7.1 is assumed not to activate it, and
            // a positive delta would create value.
            BundleId::NSM => {
                return Err(rule_violation(BundleRuleError::InactiveBundle(
                    delta.bundle.bundle_type,
                )));
            }
            _ => unreachable!("check_registered accepts only registered pairs"),
        } = value;
    }
    for effect in &effects {
        check_registered(effect.bundle, |r| r.effecting)?;
    }
    for auth in &auths {
        check_registered(auth.bundle, |r| r.authorizing)?;
    }
    let auth = |bundle_type: BundleType| {
        auths
            .binary_search_by_key(&bundle_type, |b| b.bundle.bundle_type)
            .ok()
            .map(|i| &auths[i])
    };
    let effect = |bundle_type: BundleType| {
        effects
            .binary_search_by_key(&bundle_type, |b| b.bundle.bundle_type)
            .ok()
            .map(|i| &effects[i])
    };

    let transparent_bundle = effect(BundleType::TRANSPARENT)
        .map(|effect| {
            let effects = effect.decode(|r| transparent::Effects::read(r))?;
            let input_auth = match (effects.has_inputs(), auth(BundleType::TRANSPARENT)) {
                (true, Some(auth)) => auth.decode(|r| effects.read_auth(r))?,
                (false, None) => Vec::new(),
                (true, None) => return Err(missing_auth(BundleType::TRANSPARENT)),
                (false, Some(_)) => {
                    return Err(invalid(
                        "a v7 transparent bundle without inputs has no authorizing data",
                    ));
                }
            };
            effects.into_bundle(input_auth)
        })
        .transpose()?;

    let coinbase_bundle = effect(BundleType::COINBASE)
        .map(|effect| effect.decode(CoinbaseBundle::read))
        .transpose()?;

    let sapling_bundle = shielded_bundle(
        BundleType::SAPLING,
        effect(BundleType::SAPLING),
        auth(BundleType::SAPLING),
        shielded.sapling,
        |effect, auth, value_balance| {
            let effects = effect.decode(|r| sapling_serialization::V7Effects::read(r))?;
            let auth = auth.decode(|r| effects.read_auth(r))?;
            effects.into_bundle(auth, value_balance)
        },
    )?;
    let orchard_bundle = orchard_protocol_bundle(
        BundleType::ORCHARD,
        consensus_branch_id,
        effect(BundleType::ORCHARD),
        auth(BundleType::ORCHARD),
        shielded.orchard,
    )?;
    let ironwood_bundle = orchard_protocol_bundle(
        BundleType::IRONWOOD,
        consensus_branch_id,
        effect(BundleType::IRONWOOD),
        auth(BundleType::IRONWOOD),
        shielded.ironwood,
    )?;

    TransactionData::from_parts_v7(
        consensus_branch_id,
        header.lock_time,
        BlockHeight::from_u32(header.expiry_height),
        transparent_bundle,
        sapling_bundle,
        orchard_bundle,
        ironwood_bundle,
        V7Fields {
            value_deltas,
            coinbase_bundle,
        },
    )
    .map_err(rule_violation)
}

/// Decodes a Sapling, Orchard, or Ironwood bundle, which has both effecting and
/// authorizing data, and whose balancing value is its entry in `mValuePoolDeltas`.
fn shielded_bundle<B>(
    bundle_type: BundleType,
    effect: Option<&BundleData>,
    auth: Option<&BundleData>,
    value_balance: ZatBalance,
    decode: impl FnOnce(&BundleData, &BundleData, ZatBalance) -> io::Result<B>,
) -> io::Result<Option<B>> {
    match (effect, auth) {
        (Some(effect), Some(auth)) => decode(effect, auth, value_balance).map(Some),
        (Some(_), None) => Err(missing_auth(bundle_type)),
        // The parsing rules already rule out authorizing data without effecting data.
        (None, _) if value_balance == ZatBalance::zero() => Ok(None),
        // The typed bundle carries the delta as its value balance, so the delta has
        // nowhere to go without it.
        (None, _) => Err(rule_violation(BundleRuleError::DeltaWithoutBundle(
            bundle_type,
        ))),
    }
}

fn orchard_protocol_bundle(
    bundle_type: BundleType,
    consensus_branch_id: BranchId,
    effect: Option<&BundleData>,
    auth: Option<&BundleData>,
    value_balance: ZatBalance,
) -> io::Result<Option<orchard::Bundle<orchard::bundle::Authorized, ZatBalance>>> {
    shielded_bundle(
        bundle_type,
        effect,
        auth,
        value_balance,
        |effect, auth, value_balance| {
            let bundle_version = orchard_serialization::bundle_version_for_branch(
                consensus_branch_id,
                orchard_pool(bundle_type),
            )
            .ok_or_else(|| invalid("the Orchard-protocol pool is not active in this branch"))?;
            let effects = effect.decode(|r| orchard_serialization::V7Effects::read(r))?;
            let auth = auth.decode(|r| effects.read_auth(r))?;
            effects.into_bundle(auth, value_balance, bundle_version)
        },
    )
}

fn orchard_pool(bundle_type: BundleType) -> orchard::ValuePool {
    match bundle_type {
        BundleType::ORCHARD => orchard::ValuePool::Orchard,
        BundleType::IRONWOOD => orchard::ValuePool::Ironwood,
        _ => unreachable!("only the Orchard and Ironwood bundles use the Orchard protocol"),
    }
}

/// Encodes a v7 transaction as an envelope with every payload filled in.
fn to_envelope(tx: &TransactionData<Authorized>) -> io::Result<Envelope> {
    let fields = tx
        .v7
        .as_ref()
        .expect("only v7 transaction data is written in the v7 format");
    let shielded = tx.shielded_balances();

    let mut effects = Vec::new();
    let mut auths = Vec::new();
    if let Some(bundle) = tx
        .transparent_bundle
        .as_ref()
        .filter(|b| transparent::has_effects(b))
    {
        effects.push(payload(BundleId::TRANSPARENT, |w| {
            transparent::write_effects(w, bundle)
        })?);
        if transparent::has_auth(bundle) {
            auths.push(payload(BundleId::TRANSPARENT, |w| {
                transparent::write_auth(w, bundle)
            })?);
        }
    }
    if let Some(coinbase) = &fields.coinbase_bundle {
        effects.push(payload(BundleId::COINBASE, |w| coinbase.write(w))?);
    }
    if let Some(bundle) = &tx.sapling_bundle {
        effects.push(payload(BundleId::SAPLING, |w| {
            sapling_serialization::write_v7_effects(w, bundle)
        })?);
        auths.push(payload(BundleId::SAPLING, |w| {
            sapling_serialization::write_v7_auth(w, bundle)
        })?);
    }
    for (id, bundle) in [
        (BundleId::ORCHARD, &tx.orchard_bundle),
        (BundleId::IRONWOOD, &tx.ironwood_bundle),
    ] {
        // Decoding derives the bundle version from the pool and branch, and every
        // transaction's bundles have that version, so the bundle round-trips.
        if let Some(bundle) = bundle {
            effects.push(payload(id, |w| {
                orchard_serialization::write_v7_effects(w, bundle)
            })?);
            auths.push(payload(id, |w| {
                orchard_serialization::write_v7_auth(w, bundle)
            })?);
        }
    }

    Envelope::new(
        Header {
            consensus_branch_id: tx.consensus_branch_id.into(),
            lock_time: tx.lock_time,
            expiry_height: tx.expiry_height.into(),
        },
        value_pool_deltas(&fields.value_deltas, &shielded),
        effects,
        auths,
    )
    .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e))
}

fn payload(
    bundle: BundleId,
    write: impl FnOnce(&mut Vec<u8>) -> io::Result<()>,
) -> io::Result<BundleData> {
    let mut data = Vec::new();
    write(&mut data)?;
    Ok(BundleData { bundle, data })
}

/// Checks that `bundle` is registered for v7, and that the registry permits it in the
/// map `permitted` selects.
fn check_registered(
    bundle: BundleId,
    permitted: impl FnOnce(&Registration) -> bool,
) -> io::Result<()> {
    match bundle.registration() {
        Some(registration) if permitted(&registration) => Ok(()),
        Some(_) => Err(invalid(
            "the v7 bundle registry does not permit this map entry",
        )),
        None => Err(invalid("the v7 bundle is not registered")),
    }
}

fn missing_auth(bundle_type: BundleType) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        alloc::format!("v7 bundle type {bundle_type} needs authorizing data"),
    )
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn rule_violation(error: BundleRuleError) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, error)
}
