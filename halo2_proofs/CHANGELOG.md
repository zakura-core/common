# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Prepared the `1.0.0-rc.3` release.
- `Params::new` now normalizes its inverse curve FFT with parallel batched GLV
  scalar multiplication over the already-affine generators, reducing Orchard
  `k = 11` parameter generation by 7–9% on Apple aarch64.
- The permutation- and lookup-argument provers' full-column batch inversions now
  go through a shared `batch_invert_multi` helper that splits the Montgomery
  prefix-product and back-substitution chains into interleaved lanes, with
  `ff::BatchInverter`-compatible constant-time zero handling. Batches under 32
  elements keep the single chain. Proof and verification timings are unchanged
  within noise; these inversions are a negligible share of a proof.
- Prepared the `1.0.0-rc.2` release.
- Updated the proving stack to `ff 0.14`, `group 0.14`, and `rand 0.10`.
- Forked from upstream `halo2_proofs` and renamed to `zakura-halo2-proofs`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.3.5); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
- Removed the unused `tempfile` dev-dependency inherited from upstream. Its
  `<3.7.0` cap held the workspace's `tempfile` at 3.6.0, whose `rustix 0.37`
  dependency no longer compiles on current Rust nightlies.
- The multi-opening prover and verifier now construct intermediate query sets
  in one pass.
- The multi-opening verifier now batch-inverts its Lagrange and vanishing
  denominators together, and rejects challenge collisions without panicking.
- Large single-worker Pasta multiscalar multiplications now use GLV scalar
  decomposition with signed-Booth buckets.
- The Pasta GLV Signed-Booth backend uses 10-bit windows for large
  single-worker multiscalar multiplications when its operation model favors
  them over 9-bit windows.
- Large multicore Pasta multiscalar multiplications now evaluate GLV
  signed-Booth windows in parallel when the backend cost model selects GLV.
- Batch verification now folds each proof's random batching scalar into its
  inner-product coefficient expansion.
- Common evaluation-domain rotations now bypass general exponentiation.
- Batch verification now reuses bounded per-parameter fixed-window tables when
  constructing instance commitments, with longer columns using the generic
  multiscalar multiplication path.
- Polynomial evaluation now shares missing-root products across complete
  compressed-selector families.
- Polynomial evaluation now combines compressed-selector contributions with a
  product tree, avoiding construction of every selector value separately, and
  adds unit-weighted terms without a field multiplication.
- Polynomial evaluation now caches repeated expressions whenever doing so
  avoids at least one field multiplication, and reuses cache buffers with
  disjoint lifetimes.
- Polynomial evaluation now consumes rotated polynomial chunks through
  borrowed slices when the surrounding operation can write its result directly.
- Polynomial evaluation now uses field squaring for structurally repeated
  multiplication operands.
- Polynomial evaluation now uses Horner's method for expanded fixed-base
  interpolation polynomials.
- Polynomial evaluation now shares repeated factors inside weighted constraint
  groups.
- Polynomial evaluation now caches repeated compiled subexpressions when doing
  so avoids at least three field multiplications.
- Polynomial evaluation now uses wide product accumulators when folding
  expressions over Pasta fields.
- Clarified internal vanishing-prover phase names to distinguish the random
  masking-polynomial commitment from quotient construction.
