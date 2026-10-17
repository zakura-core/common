# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [4.0.0-rc0] - 2026-10-17

### Added

- Added the default-enabled `backend-halo2` feature forwarding the Orchard
  backend selection; builds with `--no-default-features` must enable it
  ([#591](https://github.com/zakura-core/common/pull/591)).

## [3.0.0] - 2026-10-13

### Changed

- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `zcash_proofs` to `zakura-proofs`; the library target
  keeps its original name, so existing `use` paths compile unchanged.
- Replaced the `bellman` dependency with `zakura-bellman` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `bls12_381` dependency with `zakura-bls12-381` 1.0.0, whose
  types appear in this crate's API.
- Replaced the `jubjub` dependency with `zakura-jubjub` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `sapling-crypto` dependency with `zakura-sapling-crypto` 1.0.0,
  whose types appear in this crate's API.
- Replaced the `redjubjub` dependency with `zakura-redjubjub` 1.0.0.
- Replaced the `zcash_primitives` dependency with `zakura-primitives` 1.0.0.
- Updated `group` from 0.13 to 0.14 and `rand_core` from 0.6 to 0.10; the
  `SpendProver` and `OutputProver` implementations on `LocalTxProver` now take
  RNGs bound by `rand_core::Rng` instead of `rand_core::RngCore`.
- Changed the default features from `local-prover` and `multicore` to
  `multicore` alone; enable `local-prover` (or `bundled-prover`) explicitly to
  keep the `prover` module and `LocalTxProver` available.
- Raised the minimum supported Rust version from 1.88 to 1.91.

## Record of Fork

`zakura-proofs` began as a fork of the `zcash_proofs` crate and has been
developed independently in this repository since. This changelog starts at the
fork point: history up to that point is documented in the repository the code
was forked from, and this crate's version lineage restarted at `1.0.0` rather
than continuing the original `0.30.0` numbering.

- Forked from: `zcash_proofs 0.30.0`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`57b844dc`](https://github.com/zcash/librustzcash/commit/57b844dc00bf1f25254b5859b8d5faa8e5730f98).
- Imported into this repository in commit `a57d014096a67071a2c6522a160c7e0dfbeff0f4`.
