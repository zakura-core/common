# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [2.1.0-rc.0] - 2026-09-27

### Added

- Added reusable prepared keys for Sapling batch validation, avoiding
  repeated fixed G2 preparation across validators
  ([#491](https://github.com/zakura-core/common/pull/491)).

### Changed

- Sped up small mixed Spend and Output proof batches using joint prepared
  verification ([#496](https://github.com/zakura-core/common/pull/496)).
- Sped up Sapling Spend nullifier public-input packing
  ([#497](https://github.com/zakura-core/common/pull/497)).
- Sped up repeated Sapling batch validation by retaining prepared G2 terms
  inside Spend and Output verifying keys
  ([#499](https://github.com/zakura-core/common/pull/499)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `sapling-crypto` to `zakura-sapling-crypto`; the
  library target keeps its original name, so existing `use` paths compile
  unchanged.
- Updated `ff` and `group` from 0.13 to 0.14 and `rand`/`rand_core` from 0.8/0.6
  to 0.10; every RNG-accepting API (including the transaction builder, the
  prover traits, PCZT signing and proving, note encryption, and batch
  validation) now bounds its RNG parameter on the new `Rng` trait instead of
  `RngCore`, and the `test-dependencies` `Distribution<Node>` impl is now on
  `StandardUniform` instead of `Standard`.
- Replaced the `bellman` dependency with `zakura-bellman` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `bls12_381` dependency with `zakura-bls12-381` 1.0.0, whose
  types appear in this crate's API.
- Replaced the `jubjub` dependency with `zakura-jubjub` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `redjubjub` dependency with `zakura-redjubjub` 1.0.0, whose
  types appear in this crate's API.
- Replaced the public `constants::PEDERSEN_HASH_EXP_TABLE` lazy static with the
  function `constants::pedersen_hash_exp_table()`, which lazily builds and
  returns the same table as a `&'static [Vec<Vec<SubgroupPoint>>]`.
- Retained `zcash_note_encryption` 0.4, which still uses `rand_core` 0.6; the
  encryptor returned by `sapling_note_encryption` therefore takes a `rand_core`
  0.6 RNG in `encrypt_outgoing_plaintext`, even though this crate's own APIs now
  take `rand_core` 0.10 RNGs.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-sapling-crypto` began as a fork of the `sapling-crypto` crate and has
been developed independently in this repository since. This changelog starts
at the fork point: history up to that point is documented in the repository
the code was forked from, and this crate's version lineage restarted at
`1.0.0` rather than continuing the original `0.7.0` numbering.

- Forked from: `sapling-crypto 0.7.0`, published from
  [zcash/sapling-crypto](https://github.com/zcash/sapling-crypto) at commit
  [`8186b407`](https://github.com/zcash/sapling-crypto/commit/8186b407b47b595a2ea4f04c73d59fdd83bd401f).
- Imported into this repository in commit `a57d014096a67071a2c6522a160c7e0dfbeff0f4`.
