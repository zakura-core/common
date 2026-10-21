//! Malformed encodings, count bombs, boundary handling, and the deliberate
//! absence of cryptographic validation.

mod common;

use std::{fs, path::PathBuf};

use common::offset_of;
use zcash_primitives::transaction::{
    Transaction,
    tests::data::{zip_0243, zip_0244},
};
use zcash_protocol::consensus::BranchId;
use zcash_transaction_wire::{DecodeError, TransactionView};

/// The public mainnet v6 transaction with two Ironwood actions and nothing else.
fn ironwood_v6() -> Vec<u8> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/v6/main-3483367-ironwood-f337d967.hex");
    hex::decode(fs::read_to_string(path).unwrap().trim()).unwrap()
}

fn err(bytes: &[u8]) -> DecodeError {
    TransactionView::parse_exact(bytes).expect_err("must be rejected")
}

/// A v1 transaction with no inputs, the given output encodings, and lock time 0.
fn v1_with(body: &[u8]) -> Vec<u8> {
    [&[1, 0, 0, 0][..], body, &[0; 4]].concat()
}

const V5_HEADER: [u8; 8] = [0x05, 0, 0, 0x80, 0x0a, 0x27, 0xa7, 0x26];
const V6_HEADER: [u8; 8] = [0x06, 0, 0, 0x80, 0x98, 0xb6, 0x84, 0xd8];

#[test]
fn minimal_transactions_parse() {
    // No inputs, no outputs: structurally fine (a node would reject it).
    let tx = v1_with(&[0, 0]);
    let view = TransactionView::parse_exact(&tx).unwrap();
    assert!(view.transparent_inputs().is_empty() && !view.has_shielded_components());
}

#[test]
fn every_truncation_is_rejected() {
    let mut txs = vec![ironwood_v6()];
    txs.extend(zip_0243::make_test_vectors().into_iter().map(|v| v.tx));
    txs.extend(zip_0244::make_test_vectors().into_iter().map(|v| v.tx));
    for tx in txs {
        let Ok(view) = TransactionView::parse_exact(&tx) else {
            continue;
        };
        assert_eq!(view.raw(), &tx[..]);
        for len in 0..tx.len() {
            assert!(
                TransactionView::parse_prefix(&tx[..len]).is_err(),
                "a {len}-byte prefix of a {}-byte transaction parsed",
                tx.len()
            );
        }
    }
    assert!(matches!(
        err(&[]),
        DecodeError::Truncated {
            field: "header",
            needed: 4
        }
    ));
}

#[test]
fn trailing_bytes_and_prefix_boundaries() {
    let tx = ironwood_v6();
    let mut extended = tx.clone();
    extended.push(0);
    assert_eq!(err(&extended), DecodeError::TrailingBytes { count: 1 });

    let two = [&tx[..], &tx[..]].concat();
    let (first, rest) = TransactionView::parse_prefix(&two).unwrap();
    assert_eq!(first.raw(), &tx[..]);
    assert_eq!(rest, &tx[..]);
    let second = TransactionView::parse_exact(rest).unwrap();
    assert_eq!(first.txid(), second.txid());
}

#[test]
fn compact_size_must_be_canonical_and_bounded() {
    // Input count 1 encoded in three bytes.
    assert_eq!(
        err(&v1_with(&[0xfd, 0x01, 0x00, 0])),
        DecodeError::NonCanonicalCompactSize {
            field: "transparent inputs"
        }
    );
    assert_eq!(
        err(&v1_with(&[0xfe, 0xff, 0xff, 0, 0, 0])),
        DecodeError::NonCanonicalCompactSize {
            field: "transparent inputs"
        }
    );
    assert_eq!(
        err(&v1_with(&[0xff, 0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0, 0])),
        DecodeError::NonCanonicalCompactSize {
            field: "transparent inputs"
        }
    );
    // One more than MAX_COMPACT_SIZE, and the largest u64.
    assert_eq!(
        err(&v1_with(&[0xfe, 0x01, 0, 0, 0x02, 0])),
        DecodeError::CompactSizeTooLarge {
            field: "transparent inputs",
            value: 0x0200_0001
        }
    );
    assert_eq!(
        err(&v1_with(&[0xff; 9])),
        DecodeError::CompactSizeTooLarge {
            field: "transparent inputs",
            value: u64::MAX
        }
    );
}

#[test]
fn count_bombs_are_rejected_before_allocating() {
    // 0x02000000 inputs declared in a few bytes: rejected from the count alone.
    assert_eq!(
        err(&v1_with(&[0xfe, 0, 0, 0, 0x02, 0])),
        DecodeError::CountExceedsInput {
            field: "transparent inputs",
            count: 0x0200_0000
        }
    );
    // Two outputs declared with room for one.
    let one_output = [&[0, 2][..], &[0; 8], &[0]].concat();
    assert!(matches!(
        err(&v1_with(&one_output)),
        DecodeError::CountExceedsInput {
            field: "transparent outputs",
            count: 2
        }
    ));
    // A 32 MiB script length with a handful of bytes behind it.
    let huge_script = [&[0, 1][..], &[0; 8], &[0xfe, 0, 0, 0, 0x02]].concat();
    assert!(matches!(
        err(&v1_with(&huge_script)),
        DecodeError::Truncated {
            field: "scriptPubKey",
            ..
        }
    ));
    // Every 4-byte action count in a v6 transaction with no room for actions.
    let mut tx = ironwood_v6();
    let view = TransactionView::parse_exact(&tx).unwrap();
    let count_at = offset_of(&tx, view.ironwood().unwrap().actions[0].cv) - 1;
    tx.truncate(count_at);
    tx.extend([0xfe, 0, 0, 0, 0x02]);
    assert!(matches!(
        err(&tx),
        DecodeError::CountExceedsInput {
            field: "actions",
            ..
        }
    ));
}

#[test]
fn version_group_and_branch_combinations() {
    // Non-overwintered versions other than 1 and 2.
    for header in [0u32, 3, 4, 5, 6] {
        assert!(matches!(
            err(&[&header.to_le_bytes()[..], &[0; 16]].concat()),
            DecodeError::UnsupportedVersion {
                version_group_id: None,
                ..
            }
        ));
    }
    // Overwintered v4 header with the v5 group, and an unknown v7.
    let mut bad = V5_HEADER;
    bad[0] = 4;
    assert!(matches!(
        err(&[&bad[..], &[0; 16]].concat()),
        DecodeError::UnsupportedVersion { .. }
    ));
    let mut bad = V6_HEADER;
    bad[0] = 7;
    assert!(matches!(
        err(&[&bad[..], &[0; 16]].concat()),
        DecodeError::UnsupportedVersion { .. }
    ));

    let v6 = ironwood_v6();
    let with_branch = |branch: u32| {
        let mut tx = v6.clone();
        tx[8..12].copy_from_slice(&branch.to_le_bytes());
        tx
    };
    assert_eq!(
        err(&with_branch(0xdead_beef)),
        DecodeError::UnknownBranchId(0xdead_beef)
    );
    // v6 is not valid before NU6.3.
    for branch in [BranchId::Nu5, BranchId::Nu6_2, BranchId::Canopy] {
        assert_eq!(
            err(&with_branch(branch.into())),
            DecodeError::VersionNotValidInBranch {
                version: 6,
                branch_id: branch.into()
            }
        );
    }
    // v5 is not valid before NU5.
    let v5 = [
        &V5_HEADER[..],
        &u32::from(BranchId::Canopy).to_le_bytes(),
        &[0; 8 + 2 + 2 + 1],
    ]
    .concat();
    assert_eq!(
        err(&v5),
        DecodeError::VersionNotValidInBranch {
            version: 5,
            branch_id: BranchId::Canopy.into()
        }
    );
}

#[test]
fn amounts_must_be_in_range() {
    let max_money = 21_000_000u64 * 100_000_000;
    for value in [max_money + 1, u64::MAX, (-1i64) as u64] {
        let output = [&[0, 1][..], &value.to_le_bytes(), &[0]].concat();
        assert_eq!(
            err(&v1_with(&output)),
            DecodeError::ValueOutOfRange {
                field: "transparent output value"
            }
        );
    }
    let output = [&[0, 1][..], &max_money.to_le_bytes(), &[0]].concat();
    TransactionView::parse_exact(&v1_with(&output)).unwrap();

    // Ironwood value balance just outside -MAX_MONEY..=MAX_MONEY.
    let tx = ironwood_v6();
    let view = TransactionView::parse_exact(&tx).unwrap();
    let flags_at = offset_of(&tx, view.ironwood().unwrap().actions[1].out_ciphertext) + 80;
    let mut bad = tx.clone();
    bad[flags_at + 1..flags_at + 9].copy_from_slice(&(-(max_money as i64) - 1).to_le_bytes());
    assert_eq!(
        err(&bad),
        DecodeError::ValueOutOfRange {
            field: "Ironwood value balance"
        }
    );
}

#[test]
fn v4_sapling_balance_without_descriptions() {
    // v4, Sapling group, no transparent, lock time, expiry, balance 1, no
    // spends, outputs or JoinSplits.
    let tx = [
        &[0x04, 0, 0, 0x80, 0x85, 0x20, 0x2f, 0x89][..],
        &[0, 0],
        &[0; 8],
        &1i64.to_le_bytes(),
        &[0, 0, 0],
    ]
    .concat();
    assert_eq!(err(&tx), DecodeError::NonZeroBalanceWithoutDescriptions);
}

/// Moves the Ironwood bundle of the fixture into the Orchard slot.
fn as_orchard_bundle(tx: &[u8]) -> (Vec<u8>, usize) {
    let view = TransactionView::parse_exact(tx).unwrap();
    let ironwood_at = offset_of(tx, view.ironwood().unwrap().actions[0].cv) - 1;
    assert_eq!(tx[ironwood_at - 1], 0, "empty Orchard bundle");
    let moved = [&tx[..ironwood_at - 1], &tx[ironwood_at..], &[0]].concat();
    let flags_at = offset_of(tx, view.ironwood().unwrap().actions[1].out_ciphertext) + 80 - 1;
    (moved, flags_at)
}

#[test]
fn flags_follow_the_pool_rules() {
    let tx = ironwood_v6();
    let view = TransactionView::parse_exact(&tx).unwrap();
    let flags_at = offset_of(&tx, view.ironwood().unwrap().actions[1].out_ciphertext) + 80;
    assert_eq!(tx[flags_at], view.ironwood().unwrap().flags);
    for reserved in 3..8 {
        let mut bad = tx.clone();
        bad[flags_at] |= 1 << reserved;
        assert!(matches!(
            err(&bad),
            DecodeError::InvalidFlags {
                pool: "Ironwood",
                ..
            }
        ));
    }

    // The cross-address bit is allowed for Ironwood and forbidden for Orchard.
    let (mut orchard, orchard_flags_at) = as_orchard_bundle(&tx);
    orchard[orchard_flags_at] |= 0b100;
    assert!(matches!(
        err(&orchard),
        DecodeError::InvalidFlags { pool: "Orchard", .. }
    ));
    orchard[orchard_flags_at] &= !0b100;
    let view = TransactionView::parse_exact(&orchard).unwrap();
    assert!(view.orchard().is_some() && view.ironwood().is_none());
}

#[test]
fn proof_length_must_match_the_action_count() {
    let tx = ironwood_v6();
    let view = TransactionView::parse_exact(&tx).unwrap();
    let bundle = view.ironwood().unwrap();
    assert_eq!(bundle.actions.len(), 2);
    assert_eq!(bundle.proof.len(), 2720 + 2 * 2272);
    let proof_at = offset_of(&tx, bundle.proof);
    let proof_end = proof_at + bundle.proof.len();
    // Shorten the proof by one byte and re-encode its length.
    let short = (bundle.proof.len() - 1) as u16;
    let bad = [
        &tx[..proof_at - 3],
        &[0xfd],
        &short.to_le_bytes(),
        &tx[proof_at..proof_end - 1],
        &tx[proof_end..],
    ]
    .concat();
    assert_eq!(
        err(&bad),
        DecodeError::InvalidProofLength {
            pool: "Ironwood",
            expected: 7264,
            actual: 7263
        }
    );
}

/// The reader validates structure only. A commitment that is not a valid field
/// element is accepted here and rejected by Common's typed decoder.
#[test]
fn cryptographically_invalid_fields_are_accepted() {
    let mut tx = ironwood_v6();
    let view = TransactionView::parse_exact(&tx).unwrap();
    let action = view.ironwood().unwrap().actions[0];
    let cmx_at = offset_of(&tx, action.cmx);
    let rk_at = offset_of(&tx, action.rk);
    let original_txid = view.txid();
    // 2^256 - 1 exceeds the Pallas base field modulus; all-0xff is also not a
    // valid point encoding for rk.
    tx[cmx_at..cmx_at + 32].fill(0xff);
    tx[rk_at..rk_at + 32].fill(0xff);

    assert!(Transaction::read(&tx[..], BranchId::Nu6_3).is_err());
    let view = TransactionView::parse_exact(&tx).expect("structure is still valid");
    assert_eq!(view.ironwood().unwrap().actions[0].cmx, &[0xff; 32]);
    // The ID is still computed: these are effecting fields.
    assert_ne!(view.txid(), original_txid);
}
