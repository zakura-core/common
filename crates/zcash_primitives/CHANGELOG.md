# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [4.0.0] - 2026-10-20

### Added

- Added the default `pczt` feature, which gates
  `transaction::builder::DeferredPcztBuilder`, `Builder::build_for_pczt`,
  `PcztResult` and `PcztParts`, and is implied by `transparent-inputs`. Builds
  without default features that use these APIs must enable it
  ([#580](https://github.com/zakura-core/common/pull/580)).
- Added `transaction::builder::Builder::build_coinbase`, which builds a
  coinbase transaction without wallet spending keys or a fee rule through
  the existing validation and construction path; a standard transaction
  configuration fails with
  `Error::Coinbase(transparent::coinbase::Error::InvalidBuilderConfiguration)`
  ([#587](https://github.com/zakura-core/common/pull/587)).
- Added the default-enabled `backend-halo2` feature forwarding the Orchard
  backend selection; builds with `--no-default-features` must enable it
  ([#591](https://github.com/zakura-core/common/pull/591)).
- Added the default-enabled `wallet` feature gating wallet derivation and
  PCZT construction; `pczt`, `transparent-inputs`, and `test-dependencies`
  select it automatically
  ([#587](https://github.com/zakura-core/common/pull/587)).
- Added height-aware default expiry and padded shielded budget helpers for downstream wallets ([#598](https://github.com/zakura-core/common/pull/598)).

### Changed

- Renamed `DEFAULT_TX_EXPIRY_DELTA` to `PRE_NU7_DEFAULT_TX_EXPIRY_DELTA`; use `default_tx_expiry_delta` for height-aware construction ([#598](https://github.com/zakura-core/common/pull/598)).
- Default ordinary and deferred PCZT expiry to 120 blocks from the target height at NU7, preserving explicit overrides and coinbase expiry ([#598](https://github.com/zakura-core/common/pull/598)).
- Reject ordinary, PCZT, and deferred construction when padded shielded bundles exceed the NU7 per-pool or combined block budget ([#598](https://github.com/zakura-core/common/pull/598)).

### Removed

- Removed the `memuse::DynamicUsage` implementation for `BlockHash`, together with the `memuse` dependency. Code that measured it with `dynamic_usage()` no longer compiles
  ([#589](https://github.com/zakura-core/common/pull/589)).

## [3.0.0] - 2026-10-13

### Changed

- Changed the note-encryption dependency family exposed through Sapling and
  Orchard transaction/builder types to `zakura-note-encryption`, retaining
  allocation and pre-ZIP-212 support
  ([#540](https://github.com/zakura-core/common/pull/540)).
- Updated transparent dependency types to `secp256k1` 0.33 and `zcash_script`
  0.6, removing obsolete prerelease `block-buffer` and `crypto-common` pins
  ([#545](https://github.com/zakura-core/common/pull/545)).
- `transaction::builder::cached_orchard_proving_key` now returns a `Result`,
  rejecting historical circuit versions
  ([#553](https://github.com/zakura-core/common/pull/553)).
- The transaction builder no longer supports Orchard spends or outputs for
  target heights before NU6.3 activation, and coinbase transactions no longer
  include an Orchard-pool bundle
  ([#553](https://github.com/zakura-core/common/pull/553)).
- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

## [2.1.0] - 2026-09-29

### Changed

- Switched Equihash verification to the maintained `zakura-equihash` package
  ([#44](https://github.com/zakura-core/common/pull/44)).

## [2.0.0] - 2026-09-23

### Changed

- Replaced the `zcash_protocol 0.10` and `zcash_transparent 0.10` dependencies
  with `zakura-protocol` and `zakura-transparent` 2.0.0, whose types appear in
  this crate's API ([#471](https://github.com/zakura-core/common/pull/471)).
- Made NU7 select and validate V6 transactions without requiring the
  `zcash_unstable="nu7"` configuration flag
  ([#474](https://github.com/zakura-core/common/pull/474)).

### Removed

- Removed the obsolete `zip-233` Cargo feature and its V6 transaction-field
  encoding; V6 headers remain 20 bytes when `zcash_unstable="nu7"` is enabled
  ([#458](https://github.com/zakura-core/common/pull/458)).
- Removed the gated ZIP 233 APIs and constructor arguments from V6 and NU7.
  The corresponding V7 APIs remain available when
  `zcash_unstable="nutachyon"` is enabled
  ([#458](https://github.com/zakura-core/common/pull/458)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `zcash_primitives` to `zakura-primitives`; the
  library target keeps its original name, so existing `use` paths compile
  unchanged.
- Updated `ff` from 0.13 to 0.14 and `rand_core` from 0.6 to 0.10; RNG type
  parameters on the transaction builder's `build`, `build_for_pczt`, and
  `mock_build` methods now take the `Rng` trait bound in place of `RngCore`.
- Replaced the `jubjub` dependency with `zakura-jubjub` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `orchard` dependency with `zakura-orchard` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `redjubjub` dependency with `zakura-redjubjub` 1.0.0.
- Replaced the `sapling-crypto` dependency with `zakura-sapling-crypto` 1.0.0,
  whose types appear in this crate's API.
- Raised the minimum supported Rust version from 1.88 to 1.91.

## Record of Fork

`zakura-primitives` began as a fork of the `zcash_primitives` crate and has
been developed independently in this repository since. This changelog starts
at the fork point: history up to that point is documented in the repository
the code was forked from, and this crate's version lineage restarted at
`1.0.0` rather than continuing the original `0.30.0` numbering.

- Forked from: `zcash_primitives 0.30.0`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`57b844dc`](https://github.com/zcash/librustzcash/commit/57b844dc00bf1f25254b5859b8d5faa8e5730f98).
- Imported into this repository in commit `16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b`.
