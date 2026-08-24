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
   (~96 per Merkle hash)** against a 7.5 MiB precomputed table.

The old-table size is derived from 6 generators × 32 windows × 256 entries ×
160 bytes per `SubgroupPoint`, or 7,864,320 bytes. Point sizes were checked with
`std::mem::size_of` on the 64-bit benchmark targets described below.

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

Both evaluators return the same `SubgroupPoint` through the public API; only the
lookup tables and online arithmetic differ.

## Tables

Two private, lazily-built tables in `src/pedersen_hash.rs` use three chunks per
block (`C = 3`):

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
sequential accumulator chain. Tables are built with one batched field inversion per generator via
`jubjub::batch_normalize`, so lazy init stays cheap.

Table entries are also scaled by the inverse Jubjub cofactor. Three doublings
of the final sum recover the exact hash. The public path obtains its
`SubgroupPoint` through `clear_cofactor`, avoiding the full scalar
multiplication required by a checked torsion test; the internal path uses
`mul_by_cofactor` and retains the extended representation.

### Memory / speed tradeoff (`C`)

The sizes below are derived from entry counts and a 96-byte
`AffineNielsPoint`. Addition counts are for a 510-bit Merkle input plus the
six-bit personalization:

| `C` | mixed additions | fused table size |
|-----|-----------------|------------------|
|  2  |       87        |     1.37 MiB     |
|  3  |       58        |     6.18 MiB     |
|  4  |       49        |    34.03 MiB     |
|  5  |       40        |   216.28 MiB     |

`C = 3` is the shipped setting: it is the last inexpensive memory/speed jump
for node-oriented `fused-pedersen` builds, and each full 63-chunk segment
divides evenly into 21 blocks.

## Algorithm (`pedersen_hash`)

The fused evaluator buffers the input bit stream (with personalization bits
prepended) into a fixed-size stack buffer so the exact chunk count
`T = ⌈len/3⌉` is known up front. The default evaluator retains its streaming
input path and does not allocate this buffer. Both paths panic as soon as a bit
beyond the six-generator capacity arrives, so oversized or infinite inputs
fail after bounded consumption. The hash then walks chunks segment by segment
(`PEDERSEN_HASH_CHUNKS_PER_GENERATOR = 63` chunks per generator):

- Fold every full block of `C` chunks with one `PEDERSEN_HASH_BLOCK_TABLE` lookup + mixed add.
- Add any leftover chunks (the `63 mod C` tail of a segment, or the final partial segment) one
  at a time via `PEDERSEN_HASH_SINGLE_TABLE`.

For `C = 3` this is ~58 mixed additions per Merkle hash (vs ~96 full additions + the whole `Fr`
accumulation in the old code); `C = 2` is ~87 and `C = 4` is ~49.

## Point representation and API compatibility

Fast mixed addition requires an `ExtendedPoint` accumulator, and a general
checked conversion from `ExtendedPoint` to `SubgroupPoint` requires a full
scalar multiplication for the torsion check. In this implementation, the
inverse-cofactor table scaling described above makes the conversion three
doublings instead. The public `pedersen_hash` API therefore retains its
original `SubgroupPoint` return type and the guarantee encoded by that type.

An internal `pedersen_hash_extended` helper avoids the conversion in the hot
paths. `tree.rs` extracts the Merkle root coordinate directly, while
`spec.rs::windowed_pedersen_commit` uses the helper under `fused-pedersen` to
add the randomness term before performing one checked subgroup conversion.
The default commitment path continues to operate on `SubgroupPoint`s. The
fused tables and tuning constant remain private implementation details.

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

The exp-window constants
(`PEDERSEN_HASH_EXP_TABLE`, `PEDERSEN_HASH_EXP_WINDOW_SIZE`, and their builder) remain the
default. They remain available when `fused-pedersen` is enabled so Cargo feature unification
does not remove existing public API, but the exp table is not initialized unless accessed.

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

`cargo bench --bench pedersen_hash` covers the public `pedersen_hash` API for
both the 510-bit Merkle input and the 576-bit note-commitment input, plus the
production `merkle_hash` path. The public raw cases include construction of the
`SubgroupPoint` result; the Merkle case exercises the internal extended path.
Each case rotates through a fixed corpus of 1,024 pseudorandom inputs so
feature-on and feature-off runs use identical data and do not measure
per-iteration allocation. Pass `--features fused-pedersen` to compare the fused
tables with the default exp-window path.

Final measurements were taken on 2026-08-24 with Criterion 0.5.1's default
three-second warm-up, 100 samples, and approximately five-second measurement
window. Each feature mode used an optimized `cargo bench` build and the same
fixed input corpus. Times are Criterion median point estimates:

| Host and toolchain | Benchmark | Default | Fused | Speedup |
|--------------------|-----------|---------|-------|---------|
| AMD EPYC 9654 VM, x86_64, Rust 1.97.1 | public Merkle-sized raw | 37.296 µs | 13.782 µs | 2.71× |
| AMD EPYC 9654 VM, x86_64, Rust 1.97.1 | public note-sized raw | 48.645 µs | 15.669 µs | 3.10× |
| AMD EPYC 9654 VM, x86_64, Rust 1.97.1 | production `merkle_hash` | 48.153 µs | 25.061 µs | 1.92× |
| Apple M4, arm64, Rust 1.98.0 | public Merkle-sized raw | 19.025 µs | 6.751 µs | 2.82× |
| Apple M4, arm64, Rust 1.98.0 | public note-sized raw | 24.641 µs | 7.689 µs | 3.20× |
| Apple M4, arm64, Rust 1.98.0 | production `merkle_hash` | 24.311 µs | 12.247 µs | 1.99× |
