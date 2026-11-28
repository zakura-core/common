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

use core::fmt;

use zcash_protocol::{consensus::BranchId, value::ZatBalance};

use super::{registry::BundleType, transparent};
use crate::transaction::{
    Authorization, TransactionData, components::orchard::bundle_version_for_branch,
};

/// A violation of a ZIP 248 bundle-local rule by the parts of a v7 transaction.
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
