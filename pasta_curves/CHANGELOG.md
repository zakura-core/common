# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- The GLV path now recodes the two halves of the scalar decomposition as a single
  width-3 NAF over the Eisenstein integers instead of two independent width-4 wNAFs,
  cutting the shared-doubling ladder from ~51 to ~39 mixed additions. `glv::Table`
  now stores the eight digit-orbit points with the x-coordinate in all three
  endomorphism rotations (1 KiB per table, previously 512 B). The public `glv` API
  and the native constant-time `Mul` are unchanged.
- Added `glv::Table::mul_decomposed_batch`, which multiplies many points by one
  scalar on affine accumulators, batching each ladder column's field inversions
  across the batch and fusing nonzero-digit columns as affine `2P+Q`. Batches under
  512 live points, and the scalar-dependent exceptional schedules (checked exactly
  per call), fall back to the per-point ladder.
  `CurveExt::batch_mul_same_scalar_vartime` now routes through it.
- Forked from upstream `pasta_curves` and renamed to `zakura-pasta-curves`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.5.2); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
