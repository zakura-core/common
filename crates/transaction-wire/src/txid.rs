//! Transaction IDs over the borrowed fields.
//!
//! Versions 1 to 4 hash the raw encoding with SHA-256d. Versions 5 and 6 port
//! the digest traversal of `zakura_primitives::transaction::txid` and
//! `orchard::bundle::commitments` ([ZIP 244], [ZIP 229]) to raw fields; the
//! oracle tests compare every result with that implementation.
//!
//! [ZIP 244]: https://zips.z.cash/zip-0244
//! [ZIP 229]: https://zips.z.cash/zip-0229

use blake2b_simd::{Hash, Params, State};
use sha2::{Digest, Sha256};

use crate::{ActionBundle, ActionPool, SaplingBundle, TransactionView, TxVersion};

const TX_PERSONALIZATION_PREFIX: &[u8; 12] = b"ZcashTxHash_";
const HEADERS: &[u8; 16] = b"ZTxIdHeadersHash";
const TRANSPARENT: &[u8; 16] = b"ZTxIdTranspaHash";
const PREVOUTS: &[u8; 16] = b"ZTxIdPrevoutHash";
const SEQUENCE: &[u8; 16] = b"ZTxIdSequencHash";
const OUTPUTS: &[u8; 16] = b"ZTxIdOutputsHash";
const SAPLING: &[u8; 16] = b"ZTxIdSaplingHash";
const SAPLING_SPENDS: &[u8; 16] = b"ZTxIdSSpendsHash";
const SAPLING_SPENDS_COMPACT: &[u8; 16] = b"ZTxIdSSpendCHash";
const SAPLING_SPENDS_NONCOMPACT_V5: &[u8; 16] = b"ZTxIdSSpendNHash";
const SAPLING_SPENDS_NONCOMPACT_V6: &[u8; 16] = b"ZTxIdSSpendNH_v6";
const SAPLING_OUTPUTS: &[u8; 16] = b"ZTxIdSOutputHash";
const SAPLING_OUTPUTS_COMPACT: &[u8; 16] = b"ZTxIdSOutC__Hash";
const SAPLING_OUTPUTS_MEMOS: &[u8; 16] = b"ZTxIdSOutM__Hash";
const SAPLING_OUTPUTS_NONCOMPACT: &[u8; 16] = b"ZTxIdSOutN__Hash";

/// Personalizations of one Orchard-protocol bundle digest format.
struct ActionDomain {
    bundle: &'static [u8; 16],
    compact: &'static [u8; 16],
    memos: &'static [u8; 16],
    noncompact: &'static [u8; 16],
    /// Only the v5 Orchard digest commits to the anchor; v6 moves it to the
    /// authorizing digest, so changing a v6 anchor does not change the txid.
    includes_anchor: bool,
}

const ORCHARD_V5: ActionDomain = ActionDomain {
    bundle: b"ZTxIdOrchardHash",
    compact: b"ZTxIdOrcActCHash",
    memos: b"ZTxIdOrcActMHash",
    noncompact: b"ZTxIdOrcActNHash",
    includes_anchor: true,
};

// Orchard v6 reuses the v5 action-level personalizations.
const ORCHARD_V6: ActionDomain = ActionDomain {
    bundle: b"ZTxIdOrchardH_v6",
    compact: b"ZTxIdOrcActCHash",
    memos: b"ZTxIdOrcActMHash",
    noncompact: b"ZTxIdOrcActNHash",
    includes_anchor: false,
};

const IRONWOOD_V6: ActionDomain = ActionDomain {
    bundle: b"ZTxIdIronwd_H_v6",
    compact: b"ZTxIdIrnActCH_v6",
    memos: b"ZTxIdIrnActMH_v6",
    noncompact: b"ZTxIdIrnActNH_v6",
    includes_anchor: false,
};

fn hasher(personal: &[u8; 16]) -> State {
    Params::new().hash_length(32).personal(personal).to_state()
}

fn empty(personal: &[u8; 16]) -> Hash {
    hasher(personal).finalize()
}

pub(crate) fn txid(tx: &TransactionView<'_>) -> [u8; 32] {
    if tx.version <= TxVersion::V4 {
        return Sha256::digest(Sha256::digest(tx.raw)).into();
    }
    let branch_id = u32::from(tx.branch_id.expect("v5 and v6 always carry a branch ID"));
    let v6 = tx.version == TxVersion::V6;

    let mut personal = [0; 16];
    personal[..12].copy_from_slice(TX_PERSONALIZATION_PREFIX);
    personal[12..].copy_from_slice(&branch_id.to_le_bytes());

    let mut h = hasher(&personal);
    h.update(header_digest(tx, branch_id).as_bytes());
    h.update(transparent_digest(tx).as_bytes());
    h.update(
        tx.sapling
            .as_ref()
            .map_or_else(|| empty(SAPLING), |b| sapling_digest(b, v6))
            .as_bytes(),
    );
    let orchard_domain = if v6 { &ORCHARD_V6 } else { &ORCHARD_V5 };
    h.update(action_digest(tx.orchard.as_ref(), orchard_domain).as_bytes());
    if v6 {
        h.update(action_digest(tx.ironwood.as_ref(), &IRONWOOD_V6).as_bytes());
    }
    h.finalize().as_bytes().try_into().expect("32-byte hash")
}

/// ZIP 244 T.1.
fn header_digest(tx: &TransactionView<'_>, branch_id: u32) -> Hash {
    let mut h = hasher(HEADERS);
    h.update(&tx.version.header().to_le_bytes());
    h.update(
        &tx.version
            .version_group_id()
            .expect("v5 and v6 are overwintered")
            .to_le_bytes(),
    );
    h.update(&branch_id.to_le_bytes());
    h.update(&tx.lock_time.to_le_bytes());
    h.update(&tx.expiry_height.unwrap_or(0).to_le_bytes());
    h.finalize()
}

/// ZIP 244 T.2. A transaction with neither inputs nor outputs hashes the empty
/// transparent digest, as Common does for an absent transparent bundle.
fn transparent_digest(tx: &TransactionView<'_>) -> Hash {
    let mut h = hasher(TRANSPARENT);
    if !(tx.transparent_inputs.is_empty() && tx.transparent_outputs.is_empty()) {
        let mut prevouts = hasher(PREVOUTS);
        let mut sequence = hasher(SEQUENCE);
        for input in &tx.transparent_inputs {
            prevouts.update(input.prevout_txid);
            prevouts.update(&input.prevout_index.to_le_bytes());
            sequence.update(&input.sequence.to_le_bytes());
        }
        let mut outputs = hasher(OUTPUTS);
        for output in &tx.transparent_outputs {
            outputs.update(&output.value.into_u64().to_le_bytes());
            write_compact_size(&mut outputs, output.script_pubkey.len());
            outputs.update(output.script_pubkey);
        }
        h.update(prevouts.finalize().as_bytes());
        h.update(sequence.finalize().as_bytes());
        h.update(outputs.finalize().as_bytes());
    }
    h.finalize()
}

fn write_compact_size(h: &mut State, n: usize) {
    // Script lengths were read as canonical CompactSizes no larger than 0x02000000.
    let n = n as u64;
    if n < 253 {
        h.update(&[n as u8]);
    } else if n <= 0xFFFF {
        h.update(&[253]);
        h.update(&(n as u16).to_le_bytes());
    } else {
        h.update(&[254]);
        h.update(&(n as u32).to_le_bytes());
    }
}

/// ZIP 244 T.3; ZIP 229 drops the per-spend anchor from the v6 noncompact digest.
fn sapling_digest(bundle: &SaplingBundle<'_>, v6: bool) -> Hash {
    let mut spends = hasher(SAPLING_SPENDS);
    if !bundle.spends.is_empty() {
        let mut compact = hasher(SAPLING_SPENDS_COMPACT);
        let mut noncompact = hasher(if v6 {
            SAPLING_SPENDS_NONCOMPACT_V6
        } else {
            SAPLING_SPENDS_NONCOMPACT_V5
        });
        for spend in &bundle.spends {
            compact.update(spend.nullifier);
            noncompact.update(spend.cv);
            if !v6 {
                noncompact.update(spend.anchor);
            }
            noncompact.update(spend.rk);
        }
        spends.update(compact.finalize().as_bytes());
        spends.update(noncompact.finalize().as_bytes());
    }

    let mut outputs = hasher(SAPLING_OUTPUTS);
    if !bundle.outputs.is_empty() {
        let mut compact = hasher(SAPLING_OUTPUTS_COMPACT);
        let mut memos = hasher(SAPLING_OUTPUTS_MEMOS);
        let mut noncompact = hasher(SAPLING_OUTPUTS_NONCOMPACT);
        for output in &bundle.outputs {
            compact.update(output.cmu);
            compact.update(output.ephemeral_key);
            compact.update(&output.enc_ciphertext[..52]);
            memos.update(&output.enc_ciphertext[52..564]);
            noncompact.update(output.cv);
            noncompact.update(&output.enc_ciphertext[564..]);
            noncompact.update(output.out_ciphertext);
        }
        outputs.update(compact.finalize().as_bytes());
        outputs.update(memos.finalize().as_bytes());
        outputs.update(noncompact.finalize().as_bytes());
    }

    let mut h = hasher(SAPLING);
    h.update(spends.finalize().as_bytes());
    h.update(outputs.finalize().as_bytes());
    h.update(&i64::from(bundle.value_balance).to_le_bytes());
    h.finalize()
}

/// ZIP 244 T.4 for Orchard, and the ZIP 229 Orchard v6 and Ironwood variants.
fn action_digest(bundle: Option<&ActionBundle<'_>>, domain: &ActionDomain) -> Hash {
    let Some(bundle) = bundle else {
        return empty(domain.bundle);
    };
    debug_assert!(
        (bundle.pool == ActionPool::Ironwood) == core::ptr::eq(domain, &IRONWOOD_V6),
        "bundle hashed under another pool's domain"
    );
    let mut compact = hasher(domain.compact);
    let mut memos = hasher(domain.memos);
    let mut noncompact = hasher(domain.noncompact);
    for action in &bundle.actions {
        compact.update(action.nullifier);
        compact.update(action.cmx);
        compact.update(action.ephemeral_key);
        compact.update(&action.enc_ciphertext[..52]);
        memos.update(&action.enc_ciphertext[52..564]);
        noncompact.update(action.cv);
        noncompact.update(action.rk);
        noncompact.update(&action.enc_ciphertext[564..]);
        noncompact.update(action.out_ciphertext);
    }
    let mut h = hasher(domain.bundle);
    h.update(compact.finalize().as_bytes());
    h.update(memos.finalize().as_bytes());
    h.update(noncompact.finalize().as_bytes());
    h.update(&[bundle.flags]);
    h.update(&i64::from(bundle.value_balance).to_le_bytes());
    if domain.includes_anchor {
        h.update(bundle.anchor);
    }
    h.finalize()
}
