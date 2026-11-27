//! Proptest strategies for the parts of a v7 transaction that earlier versions lack.

use proptest::prelude::*;

use zcash_protocol::{
    consensus::BlockHeight,
    value::{
        ZatBalance, Zatoshis,
        testing::{arb_zat_balance, arb_zatoshis},
    },
};

use super::{
    CoinbaseBundle, MAX_COINBASE_DATA_LEN, MinerPoll, MinerSignal, V7Fields, ValueDeltas,
    rules::check_bundle_local_rules, transparent::has_effects,
};
use crate::transaction::{Authorization, TransactionData, TxVersion};

prop_compose! {
    /// An arbitrary response to a miner poll, with strictly ascending signal codes.
    pub fn arb_miner_poll()(
        codes in proptest::collection::btree_set(any::<u8>(), 1..8),
        levels in proptest::collection::vec(any::<u8>(), 8),
        poll_digest in any::<[u8; 16]>(),
    ) -> MinerPoll {
        let signals = codes
            .into_iter()
            .zip(levels)
            .map(|(signal_code, level_of_support)| MinerSignal { signal_code, level_of_support })
            .collect();
        MinerPoll::new(signals, poll_digest).expect("the signal codes are strictly ascending")
    }
}

prop_compose! {
    /// An arbitrary coinbase bundle that satisfies the rules on its own fields.
    pub fn arb_coinbase_bundle()(
        block_height in 1u32..=499_999_999,
        block_subsidy in arb_zatoshis(),
        lockbox_share in 0u64..=100,
        coinbase_data in proptest::collection::vec(any::<u8>(), 0..=MAX_COINBASE_DATA_LEN),
        miner_poll in proptest::option::of(arb_miner_poll()),
    ) -> CoinbaseBundle {
        let lockbox_value = Zatoshis::from_u64(block_subsidy.into_u64() / 100 * lockbox_share)
            .expect("a share of a valid amount is valid");
        CoinbaseBundle::new(
            BlockHeight::from_u32(block_height),
            block_subsidy,
            lockbox_value,
            coinbase_data,
            miner_poll,
        )
        .expect("the fields are in range")
    }
}

prop_compose! {
    /// Arbitrary value pool deltas. They need not balance: balancing is a consensus rule.
    pub fn arb_value_deltas()(
        transparent in arb_zat_balance(),
        coinbase in arb_zat_balance(),
        fee in arb_zat_balance(),
        nsm in arb_zat_balance(),
    ) -> ValueDeltas {
        ValueDeltas { transparent, coinbase, fee, nsm }
    }
}

prop_compose! {
    /// Arbitrary v7 fields, which need not satisfy the rules relating them to the bundles
    /// of a transaction that [`TransactionData::from_parts_v7`] checks.
    pub fn arb_v7_fields()(
        value_deltas in arb_value_deltas(),
        coinbase_bundle in proptest::option::of(arb_coinbase_bundle()),
    ) -> V7Fields {
        V7Fields { value_deltas, coinbase_bundle }
    }
}

/// Arbitrary v7 fields for a v7 transaction, and none for earlier versions.
pub fn arb_v7_fields_for_version(version: TxVersion) -> BoxedStrategy<Option<V7Fields>> {
    if version == TxVersion::V7 {
        arb_v7_fields().prop_map(Some).boxed()
    } else {
        Just(None).boxed()
    }
}

/// Adjusts arbitrary v7 data so that it satisfies the ZIP 248 bundle-local rules. A
/// coinbase transaction keeps its coinbase bundle and loses its spends: its transparent
/// inputs, and any Sapling, Orchard, or Ironwood bundle that spends. A transparent or
/// coinbase delta without its bundle is cleared.
pub(crate) fn fit_v7_fields<A: Authorization>(tx: &mut TransactionData<A>) {
    let Some(fields) = &mut tx.v7 else {
        return;
    };
    if fields.coinbase_bundle.is_some() {
        if let Some(bundle) = &mut tx.transparent_bundle {
            bundle.vin.clear();
        }
        tx.transparent_bundle = tx.transparent_bundle.take().filter(has_effects);
        tx.sapling_bundle = tx
            .sapling_bundle
            .take()
            .filter(|b| b.shielded_spends().is_empty());
        for bundle in [&mut tx.orchard_bundle, &mut tx.ironwood_bundle] {
            *bundle = bundle.take().filter(|b| !b.flags().spends_enabled());
        }
    } else {
        fields.value_deltas.coinbase = ZatBalance::zero();
    }
    if tx.transparent_bundle.is_none() {
        fields.value_deltas.transparent = ZatBalance::zero();
    }
    check_bundle_local_rules(tx).expect("the data was fitted to the rules");
}
