//! Historical mainnet and testnet blocks (Zebra's `zebra-test` vectors).
//!
//! Each block is split into transactions with `parse_prefix`, every
//! transaction is compared with Common's typed decoder, and the transaction IDs
//! must rebuild the Merkle root recorded in the block header, an expected value
//! fixed by the chain itself.

mod common;

use std::collections::BTreeMap;

use sha2::{Digest, Sha256};
use zcash_transaction_wire::{TransactionView, TxVersion};

const BLOCKS: &[(&str, &str)] = &[
    (
        "main 0 (genesis)",
        include_str!("fixtures/block-main-0-000-000.txt"),
    ),
    (
        "main 396",
        include_str!("fixtures/block-main-0-000-396.txt"),
    ),
    (
        "main 347500 (Overwinter)",
        include_str!("fixtures/block-main-0-347-500.txt"),
    ),
    (
        "main 347501",
        include_str!("fixtures/block-main-0-347-501.txt"),
    ),
    (
        "main 419201 (Sapling)",
        include_str!("fixtures/block-main-0-419-201.txt"),
    ),
    (
        "main 419202",
        include_str!("fixtures/block-main-0-419-202.txt"),
    ),
    (
        "main 1687107 (NU5)",
        include_str!("fixtures/block-main-1-687-107.txt"),
    ),
    (
        "main 1687108",
        include_str!("fixtures/block-main-1-687-108.txt"),
    ),
    (
        "test 2259",
        include_str!("fixtures/block-test-0-002-259.txt"),
    ),
    (
        "test 280001",
        include_str!("fixtures/block-test-0-280-001.txt"),
    ),
    (
        "test 1842421 (NU5)",
        include_str!("fixtures/block-test-1-842-421.txt"),
    ),
    (
        "test 1842432",
        include_str!("fixtures/block-test-1-842-432.txt"),
    ),
];

/// Block header bytes before the Equihash solution.
const HEADER_PREFIX: usize = 4 + 32 + 32 + 32 + 4 + 4 + 32;

fn sha256d(data: &[u8]) -> [u8; 32] {
    Sha256::digest(Sha256::digest(data)).into()
}

fn merkle_root(mut level: Vec<[u8; 32]>) -> [u8; 32] {
    while level.len() > 1 {
        if level.len() % 2 == 1 {
            level.push(*level.last().unwrap());
        }
        level = level
            .chunks(2)
            .map(|pair| sha256d(&[pair[0], pair[1]].concat()))
            .collect();
    }
    level[0]
}

fn compact_size(bytes: &[u8]) -> (usize, &[u8]) {
    match bytes[0] {
        n @ 0..=252 => (n as usize, &bytes[1..]),
        253 => (
            u16::from_le_bytes([bytes[1], bytes[2]]) as usize,
            &bytes[3..],
        ),
        254 => (
            u32::from_le_bytes(bytes[1..5].try_into().unwrap()) as usize,
            &bytes[5..],
        ),
        _ => unreachable!("fixtures use small counts"),
    }
}

#[test]
fn historical_blocks_match_common_and_merkle_roots() {
    let mut versions = BTreeMap::<u32, usize>::new();
    let (mut coinbase, mut sprout, mut sapling, mut orchard) = (0, 0, 0, 0);
    let mut transparent_only = 0;

    for (name, hex_block) in BLOCKS {
        let block = hex::decode(hex_block.trim()).unwrap();
        let merkle: [u8; 32] = block[36..68].try_into().unwrap();
        let (solution_len, rest) = compact_size(&block[HEADER_PREFIX..]);
        let (tx_count, mut rest) = compact_size(&rest[solution_len..]);

        let mut txids = vec![];
        for i in 0..tx_count {
            let (view, tail) = TransactionView::parse_prefix(rest)
                .unwrap_or_else(|e| panic!("{name} tx {i}: {e}"));
            assert_eq!(view.raw(), &rest[..rest.len() - tail.len()]);
            common::assert_matches_oracle(view.raw());

            *versions
                .entry(view.version().header() & 0x7FFF_FFFF)
                .or_default() += 1;
            coinbase += usize::from(view.is_coinbase());
            sprout += usize::from(view.sprout().is_some());
            sapling += usize::from(view.sapling().is_some());
            orchard += usize::from(view.orchard().is_some());
            transparent_only += usize::from(!view.has_shielded_components());
            if i == 0 {
                assert!(
                    view.is_coinbase(),
                    "{name}: first transaction is the coinbase"
                );
            }
            txids.push(view.txid());
            rest = tail;
        }
        assert!(rest.is_empty(), "{name}: bytes after the last transaction");
        assert_eq!(merkle_root(txids), merkle, "{name}: Merkle root");
    }

    println!(
        "versions {versions:?}; coinbase {coinbase}, sprout {sprout}, sapling {sapling}, \
         orchard {orchard}, transparent-only {transparent_only}"
    );
    for v in [1, 2, 3, 4, 5] {
        assert!(versions.contains_key(&v), "no historical v{v} transaction");
    }
    assert!(sprout > 0 && sapling > 0 && orchard > 0 && transparent_only > 0);
    assert_eq!(coinbase, BLOCKS.len());
}

/// The txid recorded beside Common's own testnet v4 fixture.
#[test]
fn testnet_v4_fixture_has_known_txid() {
    let tx = zcash_primitives::transaction::tests::data::tx_read_write::TX_READ_WRITE;
    let view = common::assert_matches_oracle(&tx);
    assert_eq!(view.version(), TxVersion::V4);
    let mut display = view.txid();
    display.reverse();
    assert_eq!(
        hex::encode(display),
        "64f0bd7fe30ce23753358fe3a2dc835b8fba9c0274c4e2c54a6f73114cb55639"
    );
}
