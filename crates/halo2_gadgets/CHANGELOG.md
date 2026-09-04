# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [1.1.0-rc.1] - 2026-09-03

### Added

- Added opaque APIs for preparing Sinsemilla Merkle-path arithmetic before
  assigning the corresponding circuit witnesses
  ([#340](https://github.com/zakura-core/common/pull/340)).

### Changed

- The lookup range check and running-sum decomposition gadgets now scale each
  running-sum step with a partial Montgomery reduction on Pasta fields
  ([#295](https://github.com/zakura-core/common/pull/295)).
- Changed generic fixed-base window preprocessing to advance public window
  scales iteratively instead of recomputing each power with constant-time
  exponentiation, reducing full-width Lagrange-coefficient generation by
  14.7% on Apple M4 and 16.3% on x86_64 Linux. Orchard uses precomputed
  coefficient tables, so these measurements do not represent an Orchard
  key-generation speedup
  ([#333](https://github.com/zakura-core/common/pull/333)).
- Reduced variable-base multiplication witness-generation time by precomputing
  the incomplete double-and-add chain before assigning circuit cells
  ([#337](https://github.com/zakura-core/common/pull/337)).
- Avoided redundant cell-handle clones in the variable-base multiplication
  overflow check ([#341](https://github.com/zakura-core/common/pull/341)).
- Reduced Ironwood witness-assignment time by batching unused-cell assignments
  in variable-base multiplication and retaining handles only for running sums
  consumed by later constraints
  ([#342](https://github.com/zakura-core/common/pull/342)).
- Reduced Sinsemilla witness-assignment time by batching cells whose handles
  are not consumed by later constraints
  ([#344](https://github.com/zakura-core/common/pull/344)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `halo2_gadgets` to `zakura-halo2-gadgets`; the
  library target keeps its original name, so existing `use` paths compile
  unchanged.
- Replaced the `halo2_proofs` dependency with `zakura-halo2-proofs` 1.0.0,
  whose types appear throughout this crate's API.
- Replaced the `halo2_poseidon` dependency with `zakura-halo2-poseidon` 1.0.0,
  which this crate re-exports as `poseidon::primitives`.
- Replaced the `sinsemilla` dependency with `zakura-sinsemilla` 1.0.0, which
  this crate re-exports as `sinsemilla::primitives`.
- Replaced the `pasta_curves` dependency with `zakura-pasta-curves` 1.0.0,
  whose types appear in this crate's API.
- Updated `ff` and `group` from 0.13 to 0.14; the field and curve trait bounds
  throughout the gadget APIs now come from those versions, so consumer types
  must implement the 0.14 traits.
- Sped up witness generation in the ECC, Poseidon, and Sinsemilla gadgets and
  the range-check and decomposition utilities, reducing proof creation time for
  circuits built from them.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-halo2-gadgets` began as a fork of the `halo2_gadgets` crate and has
been developed independently in this repository since. This changelog starts
at the fork point: history up to that point is documented in the repository
the code was forked from, and this crate's version lineage restarted at
`1.0.0` rather than continuing the original `0.5.0` numbering.

- Forked from: `halo2_gadgets 0.5.0`, published from
  [zcash/halo2](https://github.com/zcash/halo2) at commit
  [`d751768a`](https://github.com/zcash/halo2/commit/d751768afe0d2105b349dd93f73fde7f2eade088).
- Imported into this repository in commit `16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b`.
