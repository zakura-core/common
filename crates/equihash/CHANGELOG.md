# Changelog

All notable changes to this library will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this library adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [2.1.0-rc.0] - 2026-09-27

### Added

- Added Equihash verification and the optional Tromp CPU solver as the
  `zakura-equihash` package, preserving the `equihash` library target and
  upstream `0.3.0` public API
  ([#44](https://github.com/zakura-core/common/pull/44)).

### Changed

- Raised the minimum supported Rust version from 1.85.1 to 1.91 and adopted
  the Zakura Common workspace version and package metadata
  ([#44](https://github.com/zakura-core/common/pull/44)).
- Removed the C compiler requirement for the optional `solver` feature by
  implementing solution generation in Rust
  ([#509](https://github.com/zakura-core/common/pull/509)).
- Reduced CPU time for Equihash `(200, 9)` solution generation through the
  optional `solver` feature, with additional fast paths on supported x86-64
  CPUs
  ([#502](https://github.com/zakura-core/common/pull/502),
  [#504](https://github.com/zakura-core/common/pull/504),
  [#506](https://github.com/zakura-core/common/pull/506),
  [#508](https://github.com/zakura-core/common/pull/508),
  [#509](https://github.com/zakura-core/common/pull/509),
  [#510](https://github.com/zakura-core/common/pull/510),
  [#512](https://github.com/zakura-core/common/pull/512),
  [#513](https://github.com/zakura-core/common/pull/513),
  [#515](https://github.com/zakura-core/common/pull/515),
  [#516](https://github.com/zakura-core/common/pull/516)).
- `is_valid_solution` now rejects inputs unless `input` and `nonce` together
  are a 140-byte Zcash block header and nonce
  ([#514](https://github.com/zakura-core/common/pull/514)).
- Sped up `is_valid_solution` by about 1.7–2.9×, using AVX2 or NEON where
  available
  ([#514](https://github.com/zakura-core/common/pull/514)).

### Fixed

- `is_valid_solution` now returns an invalid-parameters error, instead of
  panicking, for `(n, k)` with `n > 512` or a collision length outside 8 to
  24 bits
  ([#514](https://github.com/zakura-core/common/pull/514)).

## Record of Fork

`zakura-equihash` began as a fork of the `equihash` crate and has been
developed independently in this repository since. This changelog starts at
the fork point: history up to that point is documented in the repository the
code was forked from, and this crate's version lineage follows the Zakura
Common workspace rather than continuing the original `0.3.0` numbering.

- Forked from: `equihash 0.3.0`, at the exact base of
  [valargroup/librustzcash#75](https://github.com/valargroup/librustzcash/pull/75),
  [zcash/librustzcash](https://github.com/zcash/librustzcash) commit
  [`3f231c7a`](https://github.com/zcash/librustzcash/commit/3f231c7ac172ca333487f5ee5ea8379b59598130).
- Imported by [#44](https://github.com/zakura-core/common/pull/44).
