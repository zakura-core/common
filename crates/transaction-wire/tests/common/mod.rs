//! Differential comparison against Common's typed decoder (`zakura-primitives`).

#![allow(dead_code)]

use zcash_primitives::transaction::Transaction;
use zcash_protocol::{consensus::BranchId, value::ZatBalance};
use zcash_transaction_wire::{ActionBundle, TransactionView, TxVersion};

/// The branch passed to Common's reader for formats without an embedded branch ID.
/// Common only uses it to label the result; it does not affect the txid.
pub fn legacy_branch(version: TxVersion) -> BranchId {
    match version {
        TxVersion::V1 | TxVersion::V2 => BranchId::Sprout,
        TxVersion::V3 => BranchId::Overwinter,
        _ => BranchId::Sapling,
    }
}

/// Parses `bytes` with both readers and asserts that every exposed field and
/// the transaction ID agree. Returns the view.
pub fn assert_matches_oracle(bytes: &[u8]) -> TransactionView<'_> {
    let view = TransactionView::parse_exact(bytes).expect("wire reader accepts");
    let branch = view
        .branch_id()
        .unwrap_or_else(|| legacy_branch(view.version()));
    let tx = Transaction::read(bytes, branch).expect("Common reader accepts");
    assert_view_matches(&view, &tx);
    view
}

pub fn assert_view_matches(view: &TransactionView<'_>, tx: &Transaction) {
    assert_eq!(&view.txid(), tx.txid().as_ref(), "txid");
    assert_eq!(view.version().header(), tx.version().header(), "header");
    assert_eq!(
        view.version().version_group_id().unwrap_or(0),
        tx.version().version_group_id()
    );
    if let Some(branch) = view.branch_id() {
        assert_eq!(branch, tx.consensus_branch_id());
    }
    assert_eq!(view.lock_time(), tx.lock_time());
    assert_eq!(
        view.expiry_height().unwrap_or(0),
        u32::from(tx.expiry_height())
    );

    // Transparent.
    let (vin, vout) = tx
        .transparent_bundle()
        .map_or((&[][..], &[][..]), |b| (&b.vin[..], &b.vout[..]));
    assert_eq!(view.transparent_inputs().len(), vin.len());
    for (w, t) in view.transparent_inputs().iter().zip(vin) {
        assert_eq!(w.prevout_txid, t.prevout().hash());
        assert_eq!(w.prevout_index, t.prevout().n());
        assert_eq!(w.script_sig, &t.script_sig().0.0[..]);
        assert_eq!(w.sequence, t.sequence());
    }
    assert_eq!(view.transparent_outputs().len(), vout.len());
    for (w, t) in view.transparent_outputs().iter().zip(vout) {
        assert_eq!(w.value, t.value());
        assert_eq!(w.script_pubkey, &t.script_pubkey().0.0[..]);
    }

    // Sprout.
    assert_eq!(
        view.sprout().map(|b| b.joinsplits.len()),
        tx.sprout_bundle().map(|b| b.joinsplits.len())
    );
    assert_eq!(
        view.sprout_value_balance(),
        tx.sprout_bundle()
            .map_or(Some(ZatBalance::zero()), |b| b.value_balance())
    );
    if let (Some(w), Some(t)) = (view.sprout(), tx.sprout_bundle()) {
        assert_eq!(w.joinsplit_pubkey, &t.joinsplit_pubkey);
        assert_eq!(w.joinsplit_sig, &t.joinsplit_sig);
    }

    // Sapling.
    assert_eq!(view.sapling().is_some(), tx.sapling_bundle().is_some());
    assert_eq!(view.sapling_value_balance(), tx.sapling_value_balance());
    if let (Some(w), Some(t)) = (view.sapling(), tx.sapling_bundle()) {
        assert_eq!(w.spends.len(), t.shielded_spends().len());
        for (ws, ts) in w.spends.iter().zip(t.shielded_spends()) {
            assert_eq!(ws.nullifier, &ts.nullifier().0);
            assert_eq!(ws.cv, &ts.cv().to_bytes());
            assert_eq!(ws.rk, &<[u8; 32]>::from(*ts.rk()));
            assert_eq!(&ws.zkproof[..], &ts.zkproof()[..]);
            assert_eq!(ws.spend_auth_sig, &<[u8; 64]>::from(*ts.spend_auth_sig()));
        }
        assert_eq!(w.outputs.len(), t.shielded_outputs().len());
        for (wo, to) in w.outputs.iter().zip(t.shielded_outputs()) {
            assert_eq!(wo.cv, &to.cv().to_bytes());
            assert_eq!(wo.cmu, &to.cmu().to_bytes());
            assert_eq!(wo.ephemeral_key, &to.ephemeral_key().0);
            assert_eq!(&wo.enc_ciphertext[..], &to.enc_ciphertext()[..]);
            assert_eq!(&wo.out_ciphertext[..], &to.out_ciphertext()[..]);
            assert_eq!(&wo.zkproof[..], &to.zkproof()[..]);
        }
        assert_eq!(
            w.binding_sig,
            &<[u8; 64]>::from(t.authorization().binding_sig)
        );
    }

    // Orchard and Ironwood.
    assert_actions_match(view.orchard(), tx.orchard_bundle());
    assert_actions_match(view.ironwood(), tx.ironwood_bundle());
    assert_eq!(
        view.orchard_value_balance(),
        tx.orchard_bundle()
            .map_or(ZatBalance::zero(), |b| *b.value_balance())
    );
    assert_eq!(
        view.ironwood_value_balance(),
        tx.ironwood_bundle()
            .map_or(ZatBalance::zero(), |b| *b.value_balance())
    );
}

fn assert_actions_match(
    w: Option<&ActionBundle<'_>>,
    t: Option<&orchard::Bundle<orchard::bundle::Authorized, ZatBalance>>,
) {
    assert_eq!(w.is_some(), t.is_some(), "action bundle presence");
    let (Some(w), Some(t)) = (w, t) else { return };
    assert_eq!(w.flags, t.flag_byte());
    assert_eq!(w.anchor, &t.anchor().to_bytes());
    assert_eq!(w.proof, t.authorization().proof().as_ref());
    assert_eq!(
        w.binding_sig,
        &<[u8; 64]>::from(t.authorization().binding_signature())
    );
    assert_eq!(w.actions.len(), t.actions().len());
    for (wa, ta) in w.actions.iter().zip(t.actions().iter()) {
        assert_eq!(wa.cv, &ta.cv_net().to_bytes());
        assert_eq!(wa.nullifier, &ta.nullifier().to_bytes());
        assert_eq!(wa.rk, &<[u8; 32]>::from(ta.rk()));
        assert_eq!(wa.cmx, &ta.cmx().to_bytes());
        assert_eq!(wa.ephemeral_key, &ta.encrypted_note().epk_bytes);
        assert_eq!(&wa.enc_ciphertext[..], &ta.encrypted_note().enc_ciphertext[..]);
        assert_eq!(&wa.out_ciphertext[..], &ta.encrypted_note().out_ciphertext[..]);
        assert_eq!(wa.spend_auth_sig, &<[u8; 64]>::from(ta.authorization()));
    }
}

/// The byte offset of `field` inside `raw`.
pub fn offset_of(raw: &[u8], field: &[u8]) -> usize {
    let start = raw.as_ptr() as usize;
    let at = field.as_ptr() as usize;
    assert!(at >= start && at + field.len() <= start + raw.len());
    at - start
}
