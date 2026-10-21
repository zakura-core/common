//! Historical mainnet and testnet fixtures.
//!
//! The blocks in `fixtures/blocks` are raw blocks copied from Zakura's
//! `zakura-test` vectors (each was fetched with `getblock <height> 0`); see
//! `fixtures/README.md`. Every transaction is read with `parse_prefix`, so the
//! transaction boundaries inside a block are exercised, and each block's
//! transaction IDs must reproduce the Merkle root the chain committed to in the
//! block header. That root is an oracle independent of both readers. Each
//! transaction is also compared field by field with Common's typed decoder.

mod common;

use std::{collections::BTreeMap, fs, path::PathBuf};

use sha2::{Digest, Sha256};
use zcash_transaction_wire::{TransactionView, TxVersion};

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn read_hex(path: &PathBuf) -> Vec<u8> {
    hex::decode(fs::read_to_string(path).unwrap().trim()).unwrap()
}

fn compact_size(bytes: &mut &[u8]) -> usize {
    let (n, len) = match bytes[0] {
        n @ 0..=252 => (u64::from(n), 1),
        253 => (
            u64::from(u16::from_le_bytes(bytes[1..3].try_into().unwrap())),
            3,
        ),
        254 => (
            u64::from(u32::from_le_bytes(bytes[1..5].try_into().unwrap())),
            5,
        ),
        255 => (u64::from_le_bytes(bytes[1..9].try_into().unwrap()), 9),
    };
    *bytes = &bytes[len..];
    n.try_into().unwrap()
}

fn sha256d(data: &[u8]) -> [u8; 32] {
    Sha256::digest(Sha256::digest(data)).into()
}

/// The Bitcoin-style Merkle root over transaction IDs in protocol byte order.
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

/// Splits a raw block into its header Merkle root and its transactions,
/// checking that the transactions end exactly at the end of the block.
fn parse_block(block: &[u8]) -> ([u8; 32], Vec<TransactionView<'_>>) {
    // version, previous block hash, Merkle root, block commitments, time, bits, nonce.
    let merkle_root: [u8; 32] = block[36..68].try_into().unwrap();
    let mut rest = &block[140..];
    let solution_len = compact_size(&mut rest);
    rest = &rest[solution_len..];
    let tx_count = compact_size(&mut rest);
    let mut txs = Vec::with_capacity(tx_count);
    for _ in 0..tx_count {
        let (view, next) = TransactionView::parse_prefix(rest).expect("historical tx parses");
        assert_eq!(view.raw().len(), rest.len() - next.len());
        rest = next;
        txs.push(view);
    }
    assert!(rest.is_empty(), "bytes after the last transaction");
    (merkle_root, txs)
}

#[test]
fn historical_blocks_match_header_merkle_roots_and_common() {
    let mut versions = BTreeMap::<(&str, TxVersion), usize>::new();
    let mut coinbase = 0;
    let mut sprout = 0;
    let mut sapling = 0;
    let mut orchard = 0;
    let mut paths: Vec<_> = fs::read_dir(fixtures().join("blocks"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    paths.sort();
    for path in &paths {
        let name = path.file_name().unwrap().to_str().unwrap();
        let network = if name.starts_with("block-main") {
            "mainnet"
        } else {
            "testnet"
        };
        let block = read_hex(path);
        let (root, txs) = parse_block(&block);
        assert!(
            txs[0].is_coinbase(),
            "{name}: first transaction is a coinbase"
        );
        let txids = txs.iter().map(TransactionView::txid).collect();
        assert_eq!(merkle_root(txids), root, "{name}: Merkle root");
        for view in &txs {
            // Re-parse through the oracle comparison, which also checks parse_exact.
            common::assert_matches_oracle(view.raw());
            *versions.entry((network, view.version())).or_default() += 1;
            coinbase += usize::from(view.is_coinbase());
            sprout += usize::from(view.sprout().is_some());
            sapling += usize::from(view.sapling().is_some());
            orchard += usize::from(view.orchard().is_some());
        }
    }
    eprintln!(
        "{} blocks: {versions:?}; coinbase {coinbase}, Sprout {sprout}, Sapling {sapling}, Orchard {orchard}",
        paths.len()
    );
    for network in ["mainnet", "testnet"] {
        for version in [
            TxVersion::V1,
            TxVersion::V2,
            TxVersion::V3,
            TxVersion::V4,
            TxVersion::V5,
        ] {
            assert!(
                versions.contains_key(&(network, version)),
                "no {network} {version:?} fixture"
            );
        }
    }
    assert!(sprout > 0 && sapling > 0 && orchard > 0);
}

/// Public mainnet v6 transactions with Ironwood actions, copied from
/// wallet-pir's fixtures. The expected IDs are the ones the node's RPC reported
/// (conventional display order), so they are independent of both readers.
#[test]
fn mainnet_ironwood_v6_transactions_match_node_txids() {
    for (file, txid, ironwood_balance, expiry) in [
        (
            "main-3483367-ironwood-f337d967.hex",
            "f337d9675817668120ae626021f61e5350ff5412beeb5e42b67bd412452b8d13",
            Some(10_000),
            Some(3_483_371),
        ),
        (
            "main-3496114-ironwood-2060cf68.hex",
            "2060cf68088b55dcd9e2f91556c72528e1ab8c6834ea3f71b8c80fca9fc51653",
            None,
            None,
        ),
    ] {
        let bytes = read_hex(&fixtures().join("v6").join(file));
        let view = common::assert_matches_oracle(&bytes);
        assert_eq!(view.version(), TxVersion::V6);
        let mut display = view.txid();
        display.reverse();
        assert_eq!(hex::encode(display), txid, "{file}");
        let ironwood = view.ironwood().expect("Ironwood actions");
        assert!(!ironwood.actions.is_empty());
        if let Some(balance) = ironwood_balance {
            // Pure Ironwood: no other pool moves value, so the balance is the fee.
            assert_eq!(i64::from(view.ironwood_value_balance()), balance);
            assert!(view.transparent_inputs().is_empty() && view.transparent_outputs().is_empty());
            assert!(view.sapling().is_none() && view.orchard().is_none());
        }
        if let Some(expiry) = expiry {
            assert_eq!(view.expiry_height(), Some(expiry));
        }
    }
}
