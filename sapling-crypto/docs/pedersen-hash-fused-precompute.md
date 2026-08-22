# Faster non-circuit Pedersen hash via fused chunk-block precomputation

## Problem

`Node::combine` (the Sapling Merkle tree hash used through `incrementalmerkletree`) and the
note-commitment hash both call `pedersen_hash` (`src/pedersen_hash.rs`). For a Merkle
`combine`, the input is 6 personalization bits + 255 (left) + 255 (right) = **516 bits → 172
three-bit chunks → 3 segments** (one generator each, 63 + 63 + 46 chunks).

The previous implementation did two things per segment:

1. **Decode + accumulate.** Each 3-bit chunk `(a, b, c)` was decoded to the scalar coefficient
   `enc · 2^{4j}` (with `enc = (1 − 2c)(1 + a + 2b) ∈ {±1, ±2, ±3, ±4}`, `j` the chunk's
   position in the segment) and summed into a jubjub `Fr` accumulator — a few field doublings
   and additions per chunk, ~172 chunks per hash.
2. **Fixed-base multiply.** `acc · G` via an 8-bit windowed table
   (`PEDERSEN_HASH_EXP_WINDOW_SIZE = 8`), i.e. 32 windows → **32 point additions per segment
   (~96 per Merkle hash)** against a ~3 MB precomputed table.

Both the `Fr` accumulation and the ~96 point additions are on the hot path of every tree
update and witness computation.

## Idea

This is fixed-base scalar multiplication against *known* generators, so we can precompute much
more aggressively. The Pedersen hash of a segment is the linear combination

```
H_g = sum_j enc(chunk_j) · 2^{4j} · G_g
```

"Unfurling" it this way (the same restructuring Orchard's Sinsemilla uses, where the boss's
"52 incomplete adds" intuition comes from) lets us **precompute each chunk's scaled point
directly** and **fold several chunks into a single table lookup**. The online cost then becomes
a handful of point additions with **no scalar-field arithmetic at all** — the entire `Fr`
accumulation loop disappears. Because this is the non-circuit path, we are free to use complete
addition and precompute without the incomplete-addition constraints the circuit must respect.

## Feature flag

The fused tables are gated by the opt-in `fused-pedersen` Cargo feature, matching
Orchard's `weighted-merkle`. Without it, `pedersen_hash` keeps the original 8-bit
exp-window tables. Enable the feature on the dependency:

```toml
sapling-crypto = { package = "zakura-sapling-crypto", features = ["fused-pedersen"] }
```

Both evaluators return the same prime-order `ExtendedPoint`; only the lookup tables
and online arithmetic differ.

## Tables

Two lazily-built tables in `src/constants.rs`, parameterised by
`PEDERSEN_HASH_CHUNKS_PER_BLOCK` (`C`, default 2):

- **`PEDERSEN_HASH_SINGLE_TABLE[g][j][raw]` = `enc · 2^{4j} · G_g`.**
  Per generator `g` (6), per chunk position `j` (0..63), indexed by the chunk's 3 raw bits
  `raw = a | b<<1 | c<<2` (8 entries). `enc` follows directly from `raw`:
  `000:+1 001:+2 010:+3 011:+4 100:−1 101:−2 110:−3 111:−4`. Tiny (6·63·8 = 3024 points).

- **`PEDERSEN_HASH_BLOCK_TABLE[g][b][raw]` = summed contribution of the `C` chunks of block
  `b`.** Per generator, per block `b` (0..⌊63/C⌋), indexed by the block's `3C` concatenated raw
  bits (chunk `k` occupies bits `3k..3k+3`). Built by **summing the relevant single-table
  entries**, so the two tables agree by construction.

Entries are stored in jubjub's **precomputed-addition (Niels) form, `AffineNielsPoint`**
(`(v+u, v−u, 2d·u·v)`, 96 bytes vs 160 for an extended point), and the accumulator is a plain
`ExtendedPoint`. Each table lookup is then a **mixed addition** (7 field multiplications, no `Z`
on the addend), which is both faster than extended+extended and, crucially, lower-latency on the
sequential accumulator chain. Tables are built with one batched field inversion per block via
`jubjub::batch_normalize`, so lazy init stays cheap.

### Memory / speed tradeoff (`C`)

Measured against the previous 8-bit-window implementation on a raw 510-bit Pedersen hash
(~20.8 µs baseline), `cargo bench --bench pedersen_hash` (`pedersen-hash`):

| `C` | time    | speedup | approx. table size |
|-----|---------|---------|--------------------|
|  2  | 10.2 µs |  2.0×   |       ~1.4 MB      |
|  3  |  6.9 µs |  3.0×   |       ~7 MB        |
|  4  |  5.9 µs |  3.5×   |       ~36 MB       |
|  5  |  4.9 µs |  4.3×   |      ~227 MB       |

`C = 2` is the default: ~2× at the smallest memory footprint (below the original exp-table's).
`C` is a one-line constant, so the operating point can be retuned later. Larger `C` gives
diminishing returns for rapidly growing memory and lazy-init cost.

## Algorithm (`pedersen_hash`)

The input bit stream (personalization bits prepended) is buffered into a `Vec<bool>` so the
exact chunk count `T = ⌈len/3⌉` is known up front. Collection is capped at one bit beyond the
fixed six-generator capacity, so oversized or infinite public-API inputs fail without unbounded
allocation. The hash then walks chunks segment by segment
(`PEDERSEN_HASH_CHUNKS_PER_GENERATOR = 63` chunks per generator):

- Fold every full block of `C` chunks with one `PEDERSEN_HASH_BLOCK_TABLE` lookup + mixed add.
- Add any leftover chunks (the `63 mod C` tail of a segment, or the final partial segment) one
  at a time via `PEDERSEN_HASH_SINGLE_TABLE`.

For `C = 2` this is ~87 mixed additions per Merkle hash (vs ~96 full additions + the whole `Fr`
accumulation in the old code); `C = 3` drops it to ~58 and `C = 4` to ~49.

## Point representation & return type (breaking change)

To use the fast mixed addition the accumulator must be an `ExtendedPoint`, and there is no cheap
`ExtendedPoint → SubgroupPoint` conversion in jubjub (only via `to_affine()`, a field
inversion). Rather than pay an inversion on every hash, **`pedersen_hash` now returns
`jubjub::ExtendedPoint`** instead of `SubgroupPoint`. This is a public API change.

Caller impact is small:

- `tree.rs` (`merkle_hash_field`) and the circuit's witness/test sites already wrapped the result
  in `ExtendedPoint::from(...)`; that wrap is now the identity and was removed.
- `spec.rs::windowed_pedersen_commit` (the note commitment, computed once per note — off the hot
  path) re-wraps the result into a `SubgroupPoint` with a single affine conversion, preserving its
  signature and everything downstream of it.

## Correctness

The result is **bit-for-bit identical** to the previous implementation — this is
consensus-critical, and the generators are protocol-fixed and unchanged.

Key invariants:

- **Exactly `T = ⌈len/3⌉` chunks are processed.** Sapling zero-pads the message to a multiple
  of 3 bits, so the final chunk's missing bits are genuine zeros (handled by indexing with
  zero-filled high bits). Chunks *beyond* the message are never added — a block is only folded
  when all `C` of its chunks are real, otherwise the tail falls back to single-chunk lookups.
- **Segment boundaries** occur every 63 chunks (a new generator); blocks never straddle them.

Guards:

- `pedersen_hash::test::test_pedersen_hash_points` — the existing Zcash consensus test vectors.
- `pedersen_hash::test::matches_reference_across_boundaries` — compares against a
  straightforward reference (accumulate-then-multiply) over many input lengths that straddle
  chunk, block, and generator boundaries (including the 6-bit personalization shift) up to the
  six-generator capacity.
- Capacity tests verify that both a one-bit-oversized input and an infinite iterator are rejected
  after bounded consumption.

Besides the return type (see above), the exp-window constants
(`PEDERSEN_HASH_EXP_TABLE`, `PEDERSEN_HASH_EXP_WINDOW_SIZE`, and their builder) remain the
default and are omitted only when `fused-pedersen` is enabled.

## Considered and rejected

- **Sign-symmetry (negation) half-table.** Flipping every chunk's sign bit negates the block sum,
  so half of each block table is redundant; storing half and conditionally negating at lookup
  halves memory. Measured, it **regressed speed ~34%** (at `C = 4`, 8.8 → 11.8 µs): the
  conditional negate lands on the sequential accumulator dependency chain and its latency
  outweighs the cache win. Kept full tables. (It remains a viable *memory-only* lever if a
  deployment ever becomes memory-bound.)
- **GLV.** Not applicable: jubjub has no efficient GLV endomorphism (its only endomorphism is
  `[−1]`, i.e. the negation above), and the hash is now a sum of precomputed table points rather
  than a scalar multiplication, so there is no scalar for GLV to decompose.

## Out of scope

- **The circuit** (`src/circuit.rs`) uses its own in-circuit Pedersen hashing with
  incomplete-addition semantics and is not touched.
- **Generators** are consensus-fixed; "better generators" does not apply to Sapling.

## Benchmarks

`cargo bench --bench pedersen_hash` covers both `pedersen-hash` (raw 510-bit hash) and
`merkle-hash` (the full `Node::combine` path via `merkle_hash`). Pass
`--features fused-pedersen` to measure the fused tables against the default
exp-window path.
