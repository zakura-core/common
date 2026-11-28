//! The ZIP 248 bundle-local rules that relate the typed parts of a v7 transaction.
//!
//! Every v7 [`Transaction`](crate::transaction::Transaction) satisfies them:
//! [`TransactionData::from_parts_v7`] checks them when it constructs v7 data, which
//! decoding does with it, and [`TransactionData::freeze`] checks them again, since
//! [`TransactionData::map_bundles`] can replace the bundles of checked data. The rules
//! that only constrain one bundle's own fields are held by that bundle's type or checked
//! when it is decoded. The rule that every signature a transparent input supplies to a
//! checksig operation uses `SIGHASH_ALL` can only be checked by running its scripts, under
//! `zcash_script`'s `Flags::SigHashAllOnly`.
//!
//! The other consensus rules are not bundle-local: a transaction that breaks one is
//! well-formed, and still decodes. [`TransactionData::check_v7_transaction_rules`] checks
//! those that one transaction decides from its header, its value pool deltas, its
//! coinbase bundle, and the counts and flags of its bundles. Full validators call it
//! before the checks that need the block or the spent outputs.

use core::fmt;

use zcash_protocol::{consensus::BranchId, value::ZatBalance};

use super::{fields::value_pool_deltas, registry::BundleType, transparent};
use crate::transaction::{
    Authorization, TransactionData, components::orchard::bundle_version_for_branch,
};

/// A violation of a ZIP 248 bundle-local rule by the parts of a v7 transaction, or a
/// bundle that typed v7 data cannot hold.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum BundleRuleError {
    /// The transaction version is unavailable in this consensus branch.
    UnsupportedBranch(BranchId),
    /// The expiry height exceeds the v7 height range.
    ExpiryHeightOutOfRange,
    /// Sapling spends have different anchors, but v7 encodes a single shared anchor.
    MixedSaplingAnchors,
    /// A value pool delta has no effecting bundle of its type.
    DeltaWithoutBundle(BundleType),
    /// A bundle is registered for v7 but not active in the transaction's consensus
    /// branch, so typed data has no place for it. This library assumes that NU7.1 does
    /// not activate the ZIP 233 bundle. Only decoding returns this error. It is a
    /// bundle availability rule, which ZIP 248 leaves out of parsing:
    /// [`Envelope`](super::Envelope) still reads such a transaction.
    InactiveBundle(BundleType),
    /// A coinbase transaction spends from the pool of this bundle type: it has
    /// transparent inputs, Sapling spends, or an Orchard or Ironwood bundle with spends
    /// enabled.
    CoinbaseSpends(BundleType),
    /// An Orchard or Ironwood bundle has the version of another pool or consensus
    /// branch. The version fixes the bundle's flag rules, such as the Orchard pool's
    /// `enableCrossAddress = 0`, and its circuit.
    WrongBundleVersion(BundleType),
}

impl fmt::Display for BundleRuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpiryHeightOutOfRange => f.write_str("v7 expiry height is out of range"),
            Self::MixedSaplingAnchors => f.write_str("v7 Sapling spends must share an anchor"),
            Self::UnsupportedBranch(branch) => write!(
                f,
                "v7 transactions are not valid in consensus branch {branch:?}"
            ),
            Self::DeltaWithoutBundle(t) => {
                write!(
                    f,
                    "the value pool delta of bundle type {t} has no effecting bundle"
                )
            }
            Self::InactiveBundle(t) => {
                write!(f, "bundle type {t} is not active in this consensus branch")
            }
            Self::CoinbaseSpends(t) => {
                write!(f, "a coinbase transaction spends from bundle type {t}")
            }
            Self::WrongBundleVersion(t) => write!(
                f,
                "the bundle of type {t} has the version of another pool or branch"
            ),
        }
    }
}

impl core::error::Error for BundleRuleError {}

/// Brings v7 transaction data into its canonical form and checks the ZIP 248
/// bundle-local rules that relate its parts. Transactions of earlier versions are
/// returned unchanged.
///
/// A v7 transparent bundle with neither inputs nor outputs is dropped, since the
/// encoding omits it.
pub(crate) fn conform<A: Authorization>(
    mut tx: TransactionData<A>,
) -> Result<TransactionData<A>, BundleRuleError> {
    if tx.v7.is_some() {
        tx.transparent_bundle = tx.transparent_bundle.filter(transparent::has_effects);
    }
    check_bundle_local_rules(&tx)?;
    Ok(tx)
}

/// Checks the ZIP 248 bundle-local rules that relate the parts of a v7 transaction.
/// Transactions of earlier versions have no such rules.
///
/// The Sapling, Orchard, and Ironwood deltas are their bundles' value balances, so they
/// cannot lack their bundles here; decoding rejects such a delta when it has no bundle to
/// carry it.
pub(crate) fn check_bundle_local_rules<A: Authorization>(
    tx: &TransactionData<A>,
) -> Result<(), BundleRuleError> {
    let Some(fields) = &tx.v7 else {
        return Ok(());
    };
    if !tx.version.valid_in_branch(tx.consensus_branch_id) {
        return Err(BundleRuleError::UnsupportedBranch(tx.consensus_branch_id));
    }
    if u32::from(tx.expiry_height()) > super::MAX_V7_HEIGHT {
        return Err(BundleRuleError::ExpiryHeightOutOfRange);
    }
    if tx.sapling_bundle().is_some_and(|bundle| {
        bundle
            .shielded_spends()
            .windows(2)
            .any(|pair| pair[0].anchor() != pair[1].anchor())
    }) {
        return Err(BundleRuleError::MixedSaplingAnchors);
    }
    let deltas = &fields.value_deltas;
    if deltas.transparent != ZatBalance::zero() && tx.transparent_bundle.is_none() {
        return Err(BundleRuleError::DeltaWithoutBundle(BundleType::TRANSPARENT));
    }
    if deltas.coinbase != ZatBalance::zero() && fields.coinbase_bundle.is_none() {
        return Err(BundleRuleError::DeltaWithoutBundle(BundleType::COINBASE));
    }
    for (bundle_type, pool, bundle) in [
        (
            BundleType::ORCHARD,
            orchard::ValuePool::Orchard,
            &tx.orchard_bundle,
        ),
        (
            BundleType::IRONWOOD,
            orchard::ValuePool::Ironwood,
            &tx.ironwood_bundle,
        ),
    ] {
        if bundle.as_ref().is_some_and(|b| {
            Some(b.bundle_version()) != bundle_version_for_branch(tx.consensus_branch_id, pool)
        }) {
            return Err(BundleRuleError::WrongBundleVersion(bundle_type));
        }
    }
    match spent_pool(tx) {
        Some(pool) if fields.coinbase_bundle.is_some() => {
            Err(BundleRuleError::CoinbaseSpends(pool))
        }
        _ => Ok(()),
    }
}

/// Returns the first pool that the transaction spends from, if any.
fn spent_pool<A: Authorization>(tx: &TransactionData<A>) -> Option<BundleType> {
    let orchard_spends = |b: &Option<orchard::Bundle<A::OrchardAuth, ZatBalance>>| {
        b.as_ref().is_some_and(|b| b.flags().spends_enabled())
    };
    [
        (
            BundleType::TRANSPARENT,
            tx.transparent_bundle
                .as_ref()
                .is_some_and(|b| !b.vin.is_empty()),
        ),
        (
            BundleType::SAPLING,
            tx.sapling_bundle
                .as_ref()
                .is_some_and(|b| !b.shielded_spends().is_empty()),
        ),
        (BundleType::ORCHARD, orchard_spends(&tx.orchard_bundle)),
        (BundleType::IRONWOOD, orchard_spends(&tx.ironwood_bundle)),
    ]
    .into_iter()
    .find_map(|(pool, spends)| spends.then_some(pool))
}

/// A violation of a consensus rule that one v7 transaction decides from its header, its
/// value pool deltas, its coinbase bundle, and the counts and flags of its bundles, found
/// by [`TransactionData::check_v7_transaction_rules`].
///
/// A transaction that breaks one of these rules is well-formed but invalid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TransactionRuleError {
    /// A coinbase transaction has a negative fee delta. It collects the fees of the other
    /// transactions in its block, so the delta is zero or positive.
    CoinbaseFeeNegative,
    /// A transaction that is not a coinbase transaction has a positive fee delta. It pays
    /// its fee out of the transparent transaction value pool, so the delta is zero or
    /// negative.
    FeePositive,
    /// The coinbase delta is not the block subsidy less the lockbox deposit and the
    /// ZIP 235 fee contribution, which is 60% of the collected fees, rounded down.
    CoinbaseDeltaMismatch,
    /// The expiry height of a coinbase transaction is not the block height in its
    /// coinbase bundle.
    CoinbaseExpiryMismatch,
    /// A coinbase transaction has an Orchard bundle. From NU6.3 a coinbase transaction
    /// has no Orchard actions; its shielded outputs go to the Sapling or Ironwood pool.
    CoinbaseOrchardActions,
    /// The Orchard or Ironwood bundle of this type has neither spends nor outputs
    /// enabled. A bundle with actions enables at least one of the two.
    NoSpendsOrOutputs(BundleType),
    /// The Orchard pool balance is negative: the transaction moves value into the Orchard
    /// pool, which has been closed to deposits since NU6.3.
    OrchardBalanceNegative,
    /// The transparent delta is below the negated total of the transparent outputs,
    /// which no spent outputs can produce, or a transaction without transparent inputs
    /// has a transparent delta that is not that negated total.
    TransparentDeltaMismatch,
    /// The transaction has no input: no coinbase bundle, transparent input, or Sapling
    /// spend, and no Orchard or Ironwood bundle with spends enabled.
    NoInputs,
    /// The transaction has no output: no transparent or Sapling output, and no Orchard or
    /// Ironwood bundle with outputs enabled.
    NoOutputs,
    /// The value pool deltas do not sum to zero, so the transaction would create or
    /// destroy value.
    Unbalanced,
}

impl fmt::Display for TransactionRuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::NoSpendsOrOutputs(t) => {
                return write!(
                    f,
                    "the bundle of type {t} has neither spends nor outputs enabled"
                );
            }
            Self::CoinbaseOrchardActions => "a coinbase transaction has Orchard actions",
            Self::CoinbaseFeeNegative => "a coinbase transaction has a negative fee delta",
            Self::FeePositive => "a non-coinbase transaction has a positive fee delta",
            Self::CoinbaseDeltaMismatch => {
                "the coinbase delta does not match the block subsidy, lockbox deposit and fees"
            }
            Self::CoinbaseExpiryMismatch => {
                "a coinbase transaction does not expire at its block height"
            }
            Self::OrchardBalanceNegative => "the Orchard pool balance is negative",
            Self::TransparentDeltaMismatch => {
                "the transparent delta does not match the transparent outputs"
            }
            Self::NoInputs => "the transaction has no inputs",
            Self::NoOutputs => "the transaction has no outputs",
            Self::Unbalanced => "the value pool deltas do not sum to zero",
        })
    }
}

impl core::error::Error for TransactionRuleError {}

/// Checks the consensus rules that one v7 transaction decides from its header, its value
/// pool deltas, its coinbase bundle, and the counts and flags of its bundles, beyond the
/// bundle-local rules that every v7 transaction already satisfies. Transactions of
/// earlier versions have no such rules here.
///
/// These are the ZIP 248 cross-bundle rules that need neither the block nor the spent
/// outputs, with the transaction consensus rules of the protocol specification that
/// ZIP 248 re-encodes or leaves unchanged for v7:
///
/// - the fee delta is not negative in a coinbase transaction, and not positive otherwise;
/// - in a coinbase transaction, the coinbase delta is the block subsidy less the lockbox
///   deposit and the fee contribution ZIP 235 removes from circulation, which is 60% of
///   the fee delta, rounded down, and the expiry height is the block height;
/// - a coinbase transaction has no Orchard actions;
/// - an Orchard or Ironwood bundle has spends or outputs enabled;
/// - the Orchard pool balance is not negative;
/// - the transparent delta is at least the negated total of the transparent outputs,
///   and equal to it without transparent inputs;
/// - the transaction has an input and an output;
/// - the value pool deltas sum to zero.
///
/// It does not verify proofs or signatures, or any rule on the contents of a shielded
/// bundle. Full validators also check what needs more context: that the coinbase
/// bundle's height, subsidy and lockbox deposit and the fee delta match the block, and
/// the transparent delta of a transaction with transparent inputs.
///
/// The coinbase delta follows ZIP 248's formula, which has no term for the value that
/// ZIP 271 pays out of the lockbox, so a v7 coinbase transaction at that payout's height
/// does not pass. On the public networks that height comes before v7 is valid.
pub(crate) fn check_transaction_local_rules<A: Authorization>(
    tx: &TransactionData<A>,
) -> Result<(), TransactionRuleError> {
    let Some(fields) = &tx.v7 else {
        return Ok(());
    };
    let zat = |value: ZatBalance| i128::from(i64::from(value));
    let deltas = &fields.value_deltas;
    let shielded = tx.shielded_balances();
    let fee = zat(deltas.fee);

    match &fields.coinbase_bundle {
        Some(coinbase) => {
            if fee < 0 {
                return Err(TransactionRuleError::CoinbaseFeeNegative);
            }
            // ZIP 235: `NSMFeeContribution = floor(6 * TransactionFees / 10)`, in force
            // from NU7, whose rules NU7.1, the only branch that permits v7, inherits. The
            // fee delta of a coinbase transaction is its block's `TransactionFees`.
            let fee_contribution = 6 * fee / 10;
            let expected = i128::from(coinbase.block_subsidy().into_u64())
                - i128::from(coinbase.lockbox_value().into_u64())
                - fee_contribution;
            if zat(deltas.coinbase) != expected {
                return Err(TransactionRuleError::CoinbaseDeltaMismatch);
            }
            if tx.expiry_height != coinbase.block_height() {
                return Err(TransactionRuleError::CoinbaseExpiryMismatch);
            }
            // > [NU6.3 onward] A coinbase transaction MUST NOT have any Orchard action
            // > descriptions.
            //
            // An Orchard bundle always has an action.
            if tx.orchard_bundle.is_some() {
                return Err(TransactionRuleError::CoinbaseOrchardActions);
            }
        }
        None if fee > 0 => return Err(TransactionRuleError::FeePositive),
        None => {}
    }

    // > If nActionsOrchard > 0, then at least one of enableSpendsOrchard and
    // > enableOutputsOrchard MUST be 1.
    //
    // The same holds for Ironwood, and a bundle always has an action.
    for (bundle_type, bundle) in [
        (BundleType::ORCHARD, &tx.orchard_bundle),
        (BundleType::IRONWOOD, &tx.ironwood_bundle),
    ] {
        if bundle.as_ref().is_some_and(|b| {
            let flags = b.flags();
            !flags.spends_enabled() && !flags.outputs_enabled()
        }) {
            return Err(TransactionRuleError::NoSpendsOrOutputs(bundle_type));
        }
    }

    if zat(shielded.orchard) < 0 {
        return Err(TransactionRuleError::OrchardBalanceNegative);
    }

    let (transparent_inputs, transparent_outputs) = tx
        .transparent_bundle
        .as_ref()
        .map_or((0, &[][..]), |bundle| (bundle.vin.len(), &bundle.vout[..]));
    let output_total: i128 = transparent_outputs
        .iter()
        .map(|output| i128::from(output.value().into_u64()))
        .sum();
    // The delta is the value of the spent outputs, which is not negative, less the
    // value of the created outputs.
    let transparent_delta = zat(deltas.transparent);
    if transparent_delta < -output_total
        || (transparent_inputs == 0 && transparent_delta != -output_total)
    {
        return Err(TransactionRuleError::TransparentDeltaMismatch);
    }

    if fields.coinbase_bundle.is_none() && spent_pool(tx).is_none() {
        return Err(TransactionRuleError::NoInputs);
    }
    let orchard_outputs = |bundle: &Option<orchard::Bundle<A::OrchardAuth, ZatBalance>>| {
        bundle.as_ref().is_some_and(|b| b.flags().outputs_enabled())
    };
    let has_outputs = !transparent_outputs.is_empty()
        || tx
            .sapling_bundle
            .as_ref()
            .is_some_and(|b| !b.shielded_outputs().is_empty())
        || orchard_outputs(&tx.orchard_bundle)
        || orchard_outputs(&tx.ironwood_bundle);
    if !has_outputs {
        return Err(TransactionRuleError::NoOutputs);
    }

    let total: i128 = value_pool_deltas(deltas, &shielded)
        .iter()
        .map(|delta| i128::from(delta.value.get()))
        .sum();
    if total != 0 {
        return Err(TransactionRuleError::Unbalanced);
    }
    Ok(())
}
