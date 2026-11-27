//! The parts of a v7 transaction that earlier transaction versions do not have.

use alloc::vec::Vec;
use core::num::NonZeroI64;

use zcash_protocol::value::ZatBalance;

use super::{coinbase::CoinbaseBundle, envelope::ValuePoolDelta, registry::BundleId};

/// The `mValuePoolDeltas` entries of a v7 transaction other than the Sapling, Orchard
/// and Ironwood balancing values.
///
/// The shielded bundles carry their balancing values as their own value balances, so
/// they are not repeated here. A zero delta is an absent entry.
///
/// It is non-exhaustive while ZIP 248 is a draft; construct it from
/// [`ValueDeltas::default`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ValueDeltas {
    /// The transparent bundle's delta: the value of the spent outputs minus the value of
    /// the created outputs.
    pub transparent: ZatBalance,
    /// The coinbase bundle's delta: the block subsidy less the lockbox deposit and the
    /// ZIP 235 fee contribution.
    pub coinbase: ZatBalance,
    /// The fee bundle's delta (ZIP 2002): the negated fee of a non-coinbase transaction,
    /// or the fees a coinbase transaction collects.
    pub fee: ZatBalance,
    /// The ZIP 233 NSM bundle's delta.
    pub nsm: ZatBalance,
}

impl Default for ValueDeltas {
    fn default() -> Self {
        Self {
            transparent: ZatBalance::zero(),
            coinbase: ZatBalance::zero(),
            fee: ZatBalance::zero(),
            nsm: ZatBalance::zero(),
        }
    }
}

/// The parts of a v7 transaction that earlier transaction versions do not have.
///
/// It is non-exhaustive while ZIP 248 is a draft; construct it from
/// [`V7Fields::default`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct V7Fields {
    /// The value pool deltas that no bundle carries as its value balance.
    pub value_deltas: ValueDeltas,
    /// The coinbase bundle, present exactly in a coinbase transaction, which spends
    /// nothing.
    pub coinbase_bundle: Option<CoinbaseBundle>,
}

/// The value balances of a v7 transaction's shielded bundles, which are their entries
/// in `mValuePoolDeltas`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ShieldedBalances {
    pub(crate) sapling: ZatBalance,
    pub(crate) orchard: ZatBalance,
    pub(crate) ironwood: ZatBalance,
}

impl Default for ShieldedBalances {
    fn default() -> Self {
        Self {
            sapling: ZatBalance::zero(),
            orchard: ZatBalance::zero(),
            ironwood: ZatBalance::zero(),
        }
    }
}

/// Assembles `mValuePoolDeltas` in encoding order, eliding zero values.
pub(crate) fn value_pool_deltas(
    value_deltas: &ValueDeltas,
    shielded: &ShieldedBalances,
) -> Vec<ValuePoolDelta> {
    [
        (BundleId::TRANSPARENT, value_deltas.transparent),
        (BundleId::COINBASE, value_deltas.coinbase),
        (BundleId::SAPLING, shielded.sapling),
        (BundleId::ORCHARD, shielded.orchard),
        (BundleId::IRONWOOD, shielded.ironwood),
        (BundleId::FEE, value_deltas.fee),
        (BundleId::NSM, value_deltas.nsm),
    ]
    .into_iter()
    .filter_map(|(bundle, value)| {
        NonZeroI64::new(i64::from(value)).map(|value| ValuePoolDelta { bundle, value })
    })
    .collect()
}
