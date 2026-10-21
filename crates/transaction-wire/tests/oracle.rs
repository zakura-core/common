//! Differential tests against Common's typed decoder and its published vectors.

mod common;

use common::{assert_matches_oracle, offset_of};
use proptest::prelude::*;
use zcash_primitives::transaction::{
    Transaction,
    testing::arb_tx,
    tests::data::{zip_0143, zip_0243, zip_0244},
};
use zcash_protocol::consensus::BranchId;
use zcash_transaction_wire::{TransactionView, TxVersion};

fn encode(tx: &Transaction) -> Vec<u8> {
    let mut bytes = vec![];
    tx.write(&mut bytes).unwrap();
    bytes
}

/// ZIP 143 (v3) and ZIP 243 (v4) vectors: random but structurally valid
/// transactions whose IDs are SHA-256d of the encoding.
#[test]
fn zip_0143_and_0243_vectors_match_common() {
    let mut seen = 0;
    for tx in zip_0143::make_test_vectors()
        .into_iter()
        .map(|v| v.tx)
        .chain(zip_0243::make_test_vectors().into_iter().map(|v| v.tx))
    {
        match TransactionView::parse_exact(&tx) {
            Ok(_) => {
                assert_matches_oracle(&tx);
                seen += 1;
            }
            // These generated vectors pre-date the rule that an empty Sapling
            // bundle must have a zero value balance; Common's reader drops the
            // balance, this reader rejects it (see the README).
            Err(zcash_transaction_wire::DecodeError::NonZeroBalanceWithoutDescriptions) => {}
            Err(e) => panic!("unexpected rejection: {e}"),
        }
    }
    assert!(seen >= 10, "only {seen} vectors parsed");
}

/// ZIP 244 (v5) vectors carry fixed expected transaction IDs.
#[test]
fn zip_0244_vectors_match_fixed_txids() {
    for tv in zip_0244::make_test_vectors() {
        let view = assert_matches_oracle(&tv.tx);
        assert_eq!(view.version(), TxVersion::V5);
        assert_eq!(view.txid(), tv.txid);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn arbitrary_transactions_match_common(
        tx in prop_oneof![
            arb_tx(BranchId::Sprout),
            arb_tx(BranchId::Overwinter),
            arb_tx(BranchId::Sapling),
            arb_tx(BranchId::Canopy),
            arb_tx(BranchId::Nu5),
            arb_tx(BranchId::Nu6_2),
            arb_tx(BranchId::Nu6_3),
            arb_tx(BranchId::Nu7),
        ]
    ) {
        let bytes = encode(&tx);
        assert_matches_oracle(&bytes);
    }

    /// V6 with every pool present, so Orchard and Ironwood are both exercised.
    #[test]
    fn v6_transactions_match_common(tx in arb_tx(BranchId::Nu6_3)) {
        let bytes = encode(&tx);
        let view = assert_matches_oracle(&bytes);
        prop_assert_eq!(view.version(), TxVersion::V6);
    }

    /// ZIP 244 and ZIP 229: authorizing data (proofs, signatures) is outside the
    /// transaction ID and effecting data is inside it. Anchors are effecting in
    /// v5 but authorizing in v6. Each mutation is checked against Common too.
    #[test]
    fn authorizing_mutations_keep_txid_effecting_mutations_change_it(
        tx in prop_oneof![arb_tx(BranchId::Nu5), arb_tx(BranchId::Nu6_3)],
    ) {
        let bytes = encode(&tx);
        let view = TransactionView::parse_exact(&bytes).unwrap();
        let txid = view.txid();
        let v6 = view.version() == TxVersion::V6;

        let mut auth_offsets = vec![];
        let mut effect_offsets = vec![];
        let mut anchor_offsets = vec![];
        if let Some(s) = view.sapling() {
            if let Some(spend) = s.spends.first() {
                anchor_offsets.push(offset_of(&bytes, spend.anchor));
                auth_offsets.push(offset_of(&bytes, spend.zkproof));
                auth_offsets.push(offset_of(&bytes, spend.spend_auth_sig));
                effect_offsets.push(offset_of(&bytes, spend.nullifier));
            }
            if let Some(output) = s.outputs.first() {
                auth_offsets.push(offset_of(&bytes, output.zkproof));
                effect_offsets.push(offset_of(&bytes, output.enc_ciphertext));
            }
            auth_offsets.push(offset_of(&bytes, s.binding_sig));
        }
        for bundle in [view.orchard(), view.ironwood()].into_iter().flatten() {
            anchor_offsets.push(offset_of(&bytes, bundle.anchor));
            auth_offsets.push(offset_of(&bytes, bundle.proof));
            auth_offsets.push(offset_of(&bytes, bundle.binding_sig));
            auth_offsets.push(offset_of(&bytes, bundle.actions[0].spend_auth_sig));
            effect_offsets.push(offset_of(&bytes, bundle.actions[0].enc_ciphertext));
            effect_offsets.push(offset_of(&bytes, bundle.actions[0].out_ciphertext));
        }
        if v6 {
            auth_offsets.extend(anchor_offsets);
        } else {
            effect_offsets.extend(anchor_offsets);
        }
        if let Some(input) = view.transparent_inputs().first() {
            // scriptSig is authorizing data in v5/v6.
            if !input.script_sig.is_empty() {
                auth_offsets.push(offset_of(&bytes, input.script_sig));
            }
            effect_offsets.push(offset_of(&bytes, input.prevout_txid));
        }

        for (offsets, changes) in [(auth_offsets, false), (effect_offsets, true)] {
            for at in offsets {
                let mut mutated = bytes.clone();
                mutated[at] ^= 1;
                // Anchors and other fields may stop being valid field elements;
                // skip mutations Common's typed decoder cannot represent.
                let Ok(oracle) = Transaction::read(&mutated[..], view.branch_id().unwrap()) else {
                    continue;
                };
                let mutated_view = TransactionView::parse_exact(&mutated).unwrap();
                common::assert_view_matches(&mutated_view, &oracle);
                prop_assert_eq!(mutated_view.txid() != txid, changes, "offset {}", at);
            }
        }
    }
}
