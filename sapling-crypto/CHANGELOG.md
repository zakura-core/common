# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Opt-in `fused-pedersen` feature, which caches fused chunk-block lookup tables
  (~1.4 MiB at the default `PEDERSEN_HASH_CHUNKS_PER_BLOCK`) to speed up
  non-circuit Pedersen hashing by about 2x. The default remains the original
  8-bit exp-window tables. When the feature is enabled, `sapling_crypto::constants`
  also exposes:
  - `PEDERSEN_HASH_CHUNKS_PER_BLOCK`
  - `PEDERSEN_HASH_SINGLE_TABLE`
  - `PEDERSEN_HASH_BLOCK_TABLE`

### Changed

- `sapling_crypto::pedersen_hash::pedersen_hash` now returns a
  `jubjub::ExtendedPoint` instead of a `jubjub::SubgroupPoint`. The returned
  point is still in the prime-order subgroup; callers that need a
  `SubgroupPoint` can re-derive one (e.g. via `to_bytes`/`from_bytes`). With
  `fused-pedersen`, this avoids an inversion on the mixed-addition hot path.

### Removed

- When `fused-pedersen` is enabled, `sapling_crypto::constants::PEDERSEN_HASH_EXP_TABLE`
  and `PEDERSEN_HASH_EXP_WINDOW_SIZE` are not present.

- Prepared the `1.0.0-rc.3` release.
- Prepared the `1.0.0-rc.2` release.
- Updated to `ff 0.14`, `group 0.14`, `rand 0.10`, and the Zakura Groth16 and
  Jubjub forks.
- Forked from upstream `sapling-crypto` and renamed to `zakura-sapling-crypto`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.7.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
