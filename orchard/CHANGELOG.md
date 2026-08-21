# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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
