# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Prepared the `1.0.0-rc.4` release.
- Sped up Orchard proving- and verifying-key construction by loading the
  deterministic `k = 11` Halo 2 parameters from their canonical encoding
  instead of regenerating them for every key.
- Added `circuit::ProvingKey::prepare_proving`, which builds and caches
  prepared fixed-base commitment tables over the key's SRS (see
  `halo2_proofs::poly::commitment::Params::prepare_commitments`).
  Long-lived provers should call it once per key; arming never slows
  proving down (the prepared route is used only on pools of at most eight
  effective threads, where it wins).
- Added an opt-in `orbits` feature that enables halo2's prepared fixed-base
  MSM backend. With the feature enabled, the Orchard prover benchmark arms
  `circuit::ProvingKey::prepare_proving` before its timed routine.
- Kept the cached-plan witness-assignment benchmark lint-clean on current Rust
  toolchains.
- Added `circuit::VerifyingKey::prepare_batch_validation`, which builds and
  caches a prepared fixed-base zero-check over the key's SRS (see
  `halo2_proofs::poly::commitment::Params::prepare_zero_checks`) and
  returns whether one was actually armed (`false` when halo2 was built
  without its opt-in `orbits` feature or its backend declined).
  Long-lived validators should call it once per key: the halo2 verifier's
  final identity test then routes through the preparation, and a
  `BatchValidator` batch pays a single such check. The prepared check is
  used on pools of at most eight effective threads; verification falls
  back to the unprepared path on wider pools, so arming never slows
  validation down. Measured end to end on
  Ironwood bundle batch validation, arming the key speeds small batches
  the most (about +22% at one bundle serially and +29% on an 8-worker
  pool — 32-worker cells drift too much between processes to quote —
  tapering as per-proof transcript and signature work dominates larger
  batches).
- Added an ignored `ironwood_batch_timings` integration test: a manual
  timing harness validating batches of real Ironwood bundles through
  `BatchValidator` across batch sizes and worker counts.
- Added a reusable cached-plan Orchard witness-assignment benchmark for one,
  two, and four Actions.
- Multi-Action proof creation now synthesizes independent Action witnesses in
  parallel when the `multicore` feature is enabled.
- The `visibility` dependency is now optional and only enabled by the
  `unstable-voting-circuits` feature, which is the only place it was used.
- Replaced `lazy_static` with `once_cell` for the lazily-built Merkle CRH
  domain, note commitment domain, and empty-roots tables, using an
  exactly-once initialization wrapper so concurrent first use cannot build a
  table more than once. This also fixes a latent bug where the crate
  declared `lazy_static` without `spin_no_std` despite `#![no_std]`.

- Added a reproducible Orchard proving-key benchmark and configurable worker
  counts for the one-, two-, and four-Action prover benchmarks.
- Added `MerkleHashBatchWorkspace` and
  `MerkleHashOrchard::combine_batch_with_workspace` under the
  `weighted-merkle` feature so repeated batched tree hashing can retain its
  temporary allocations.
- Prepared the `1.0.0-rc.3` release.
- Orchard proving-key generation now uses precomputed fixed-base Lagrange
  coefficients instead of recomputing them during every circuit synthesis.
  The generated table's header now carries its regeneration command, and both
  the generator and the equivalence test take each base's window count from
  its `FixedScalarKind`, as the `FixedPoint::lagrange_coeffs` default does.
- The `merkle` benchmark gained `4096-leaves-distinct` and
  `4096-leaves-distinct-batch`: a 2^12-leaf tree of seeded pseudorandom leaves
  drawn with repeats rejected, so every leaf is distinct by construction,
  generated once and cloned per sample outside the measurement. The
  `1024-leaves` cases are unchanged.
- `MerkleHashOrchard::combine_batch` is now pinned directly to fixed vectors:
  the protocol's empty roots at every level, the zcash-test-vectors Merkle
  path trees (every internal node checked, in per-tree and cross-tree batches),
  the zcashd-derived anchor through all 32 levels, and a deterministic
  2,048-leaf edge-case tree (special field values, single-bit and
  single-Sinsemilla-word patterns, empty roots) whose nodes are recorded in
  `test_vectors/merkle_fixture.rs`.
- The weighted Merkle word decoder's equivalence tests now include
  deterministic edge vectors (all-zero and all-one bit patterns, both ends of
  the canonical range, dense and alternating limbs) alongside the random
  property test, pinning the decoder's mask and shift boundaries.
- Prepared the `1.0.0-rc.2` release.
- Updated the curve stack to `ff 0.14`, `group 0.14`, and `rand 0.10`.
- Added `MerkleHashOrchard::combine_batch` for same-level Merkle node pairs,
  sharing projective-to-affine normalization across each batch.
- Weighted `MerkleHashOrchard::combine_batch` now delegates complete batch
  evaluation to `zakura-sinsemilla`, improving generator-table locality.
- Weighted Merkle hashing now decodes its fixed 52-word input directly from
  child field encodings instead of iterating through individual bits.
- The Sinsemilla Merkle CRH domain is now initialized once and reused for
  Orchard and Ironwood commitment-tree hashing instead of deriving the same
  generator for every node.
- Added `ProvingKey::verifying_key` to reuse the verifying key generated as
  part of proving-key construction.
- Added the opt-in `weighted-merkle` feature, which reuses a cached 52-word
  position-weighted Sinsemilla domain and omits incomplete-addition checks that
  are assumed infeasible under the discrete-logarithm relation (DLR)
  assumption. The default remains the lower-memory generic fused Sinsemilla
  evaluator with exact partial-function semantics.
- Batch trial-decryption key agreement now multiplies all of a batch's prepared
  ephemeral keys by each viewing key in one synchronized GLV call, picking up the
  batched-inversion affine ladder in `pasta_curves` for large scans. Trial
  decryption of undecryptable outputs (the wallet-scanning hot case) is about 9%
  faster end to end from the accompanying `pasta_curves` recoding change.
- Added reproducible one-Action prover and validated-corpus batch-verifier
  benchmark harnesses.
- The Sinsemilla note-commitment domain is now initialized once and reused
  instead of deriving the same generators for every commitment.
- Forked from upstream `orchard` and renamed to `zakura-orchard`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.15.5); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
