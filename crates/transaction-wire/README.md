# zakura-transaction-wire (prototype)

An experimental, unpublished (`publish = false`) reader for the Zcash
transaction wire format, versions 1 to 6. It checks that bytes are a
structurally valid transaction, exposes every field as a borrowed slice of the
input, and computes the exact transaction ID. Its only Common dependency is
`zakura-protocol`; it pulls in no Sapling, Orchard, Halo2, primitives, wallet
or node crate, so a service that only needs transaction fields can avoid
compiling the proving stack.

This is a prototype for evaluating that approach. Common's typed decoder
(`zakura-primitives`) and its users are unchanged, and the API may change.

## API

```rust
use zcash_transaction_wire::{TransactionView, DecodeError};

// One transaction from the start of a buffer (e.g. a block body), plus the rest.
let (tx, rest) = TransactionView::parse_prefix(bytes)?;
// Exactly one transaction; trailing bytes are an error.
let tx = TransactionView::parse_exact(bytes)?;

let id: [u8; 32] = tx.txid(); // protocol byte order; reverse for display
```

`TransactionView<'a>` provides:

| Method | Returns |
| --- | --- |
| `raw()` | the exact consumed bytes |
| `version()` | `TxVersion::V1..=V6` (`number()`, `header()`, `version_group_id()`) |
| `branch_id()` | embedded `BranchId` (v5/v6 only) |
| `lock_time()`, `expiry_height()` | `u32`, `Option<u32>` (v3+) |
| `transparent_inputs()` | `TransparentInput { prevout_txid, prevout_index, script_sig, sequence }` |
| `transparent_outputs()` | `TransparentOutput { value: Zatoshis, script_pubkey }` |
| `is_coinbase()` | one input with the null outpoint (shape only) |
| `sprout()` | `SproutBundle { joinsplits: [JoinSplit { vpub_old, vpub_new, nullifiers, commitments, .. }], .. }` |
| `sapling()` | `SaplingBundle { spends: [SaplingSpend { nullifier, cv, rk, anchor, .. }], outputs: [SaplingOutput { cmu, ephemeral_key, enc_ciphertext, out_ciphertext, .. }], value_balance, .. }` |
| `orchard()`, `ironwood()` | `ActionBundle { pool, actions: [Action { cv, nullifier, rk, cmx, ephemeral_key, enc_ciphertext /*580*/, out_ciphertext /*80*/, .. }], flags, value_balance, anchor, proof, binding_sig }` |
| `has_shielded_components()` | any shielded pool has descriptions |
| `sprout_value_balance()` | `Option<ZatBalance>`: `None` if a partial sum leaves the money range |
| `sapling_value_balance()`, `orchard_value_balance()`, `ironwood_value_balance()` | `ZatBalance`, zero when the pool is absent |

Amounts use `zakura-protocol`'s `Zatoshis` (`0..=MAX_MONEY`) and `ZatBalance`
(`-MAX_MONEY..=MAX_MONEY`). Shielded fields are raw byte arrays, not curve or
field types. Only the per-element metadata vectors allocate, and each element
count is checked against the remaining input before allocating.

## Trust boundary

A successful parse means the bytes follow the wire grammar, nothing more.

Checked: canonical CompactSize encodings no larger than `0x02000000`; the
header, version group and (v5/v6) branch ID combination; amount ranges;
field lengths; the Sapling zero-balance rule for empty v4 bundles; per-pool
flag bits (bits 3..7 never set, cross-address bit only for Ironwood); the
canonical Orchard/Ironwood proof length (except Orchard before NU6.2, as in
Common); exact transaction boundaries and, for `parse_exact`, trailing bytes.
Malformed input returns `DecodeError`; it never panics.

**Not checked**: whether commitments, keys, nullifiers and ephemeral keys are
valid curve points or canonical field elements; proofs; signatures; and every
contextual consensus rule (branch ID vs height, fees, coinbase rules, scripts,
expiry, input existence). Bytes such as an all-`0xff` `cmx` or `rk` are
accepted here although Common's typed decoder rejects them (see
`cryptographically_invalid_fields_are_accepted` in `tests/malformed.rs`).
Do not treat a parsed transaction as a valid one. A transaction taken from a
node's block or mempool was validated by that node; one from anywhere else was
not.

## Transaction IDs

Versions 1 to 4 use SHA-256d of the encoding. Versions 5 and 6 port the
[ZIP 244] and [ZIP 229] digest tree from `zakura_primitives::transaction::txid`
and `orchard::bundle::commitments` to the raw fields, including the separate
Orchard v6 and Ironwood personalizations and the v6 move of anchors from the
effecting to the authorizing digest. ZIP 229 is a draft; this crate follows
Common, which the tests use as the oracle. Its personalization strings, the
omitted v6 Sapling, Orchard and Ironwood anchors, and the proof length rule
were compared with the ZIP 229 text published on 2026-10-21 and agree.

## Tests

- `tests/historical.rs`: 13 mainnet and testnet blocks (v1 to v5; coinbase,
  Sprout, Sapling, Orchard) from Zakura's `zakura-test` vectors. Every
  transaction is split with `parse_prefix`, the IDs must reproduce each
  header's Merkle root, and every field is compared with Common's typed
  decoder. Two public mainnet v6 Ironwood transactions are checked against the
  IDs the node's RPC reported. Fixture sources: `tests/fixtures/README.md`.
- `tests/oracle.rs`: ZIP 143/243/244 vectors and generated v1 to v6
  transactions compared with Common; authorizing vs effecting mutations for v5
  and v6.
- `tests/malformed.rs`: truncation at every length, trailing bytes, prefix
  boundaries, non-canonical and oversized CompactSize, count bombs, version,
  group and branch combinations, amount ranges, flags, proof lengths, and the
  lack of cryptographic validation.
- `tests/dependencies.rs`: runs `cargo tree` and fails if a normal or build
  dependency is a shielded, proving, primitives, wallet or node crate.

`zakura-primitives` and `zakura-orchard` are dev-dependencies only.

## Limitations and future work

- `PoolNotActive` is unreachable today: v5 requires NU5 and v6 requires NU6.3,
  where both pools are active. It is kept as a defensive check.
- Common's typed decoder silently drops a non-zero balance on an empty v4
  Sapling bundle, while this reader rejects it (some generated ZIP 243 vectors
  have this shape; none of the historical fixtures does).
- Moving Common's typed decoder onto this reader, so the digest traversal
  exists once, is future work.

[ZIP 244]: https://zips.z.cash/zip-0244
[ZIP 229]: https://zips.z.cash/zip-0229
