# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

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
  encoding; V6 headers remain 20 bytes
  ([#458](https://github.com/zakura-core/common/pull/458)).
- Removed the gated `TxVersion::has_zip233`, `TransactionData::zip233_amount`,
  and `Builder::set_zip233_amount` APIs, plus the amount arguments on
  `TransactionData::from_parts`, `TransactionData::from_parts_v6`, and
  `TransactionDigest::digest_header`. Consumers of the old opt-in API must
  remove those calls and arguments
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
