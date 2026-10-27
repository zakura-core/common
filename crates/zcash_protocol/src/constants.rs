//! Network-specific Zcash constants.

pub mod mainnet;
pub mod regtest;
pub mod testnet;

/// Domain separator for experimental WOTS public-key commitments.
///
/// The committed encoding contains the public seed followed by the ordered chain endpoints.
// TODO: Specify this tag and the canonical key encoding in the protocol specification
// before enabling WOTS on a public network.
pub const WOTS_KEY_COMMITMENT_DOMAIN: &[u8] = b"Zcash/WOTS/key/v1";

/// Domain separator for the Merkle nodes committing to one account step's spare keys.
pub const PQ_KEY_SET_NODE_DOMAIN: &[u8] = b"Zcash/PQ/node/v1";

// The `V<n>_TX_VERSION` constants, although trivial, serve to clarify that a
// transaction version is meant in APIs that use a bare `u32`. Consider using
// `zcash_primitives::transaction::TxVersion` instead.

/// Transaction version 3, which was introduced by the Overwinter network upgrade
/// and allowed until Sapling activation. It is specified in
/// [§ 7.1 Transaction Encoding and Consensus](https://zips.z.cash/protocol/protocol.pdf#txnencoding).
///
/// This constant is called `OVERWINTER_TX_VERSION` in the zcashd source.
pub const V3_TX_VERSION: u32 = 3;
/// The version group ID for Zcash v3 transactions.
///
/// This constant is called `OVERWINTER_VERSION_GROUP_ID` in the zcashd source.
pub const V3_VERSION_GROUP_ID: u32 = 0x03C48270;

/// Transaction version 4, which was introduced by the Sapling network upgrade.
/// It is specified in [§ 7.1 Transaction Encoding and Consensus](https://zips.z.cash/protocol/protocol.pdf#txnencoding).
///
/// This constant is called `SAPLING_TX_VERSION` in the zcashd source.
pub const V4_TX_VERSION: u32 = 4;
/// The version group ID for Zcash v4 transactions.
///
/// This constant is called `SAPLING_VERSION_GROUP_ID` in the zcashd source.
pub const V4_VERSION_GROUP_ID: u32 = 0x892F2085;

/// Transaction version 5, which was introduced by the NU5 network upgrade.
/// It is specified in [§ 7.1 Transaction Encoding and Consensus](https://zips.z.cash/protocol/protocol.pdf#txnencoding)
/// and [ZIP 225](https://zips.z.cash/zip-0225).
pub const V5_TX_VERSION: u32 = 5;
/// The version group ID for Zcash v5 transactions.
pub const V5_VERSION_GROUP_ID: u32 = 0x26A7270A;

/// Transaction version 6, specified in [ZIP 229](https://zips.z.cash/zip-0229).
pub const V6_TX_VERSION: u32 = 6;
/// The version group ID for Zcash v6 transactions.
pub const V6_VERSION_GROUP_ID: u32 = 0xD884B698;

/// The maximum size in bytes of a Zcash block, and therefore the maximum size of any single
/// transaction within one.
///
/// It is specified as `MAX_BLOCK_SIZE` in
/// [§ 7.6 Block Header Encoding and Consensus](https://zips.z.cash/protocol/protocol.pdf#blockheader).
///
/// This constant is called `MAX_BLOCK_SIZE` in the zcashd source.
pub const MAX_BLOCK_BYTES: usize = 2_000_000;
