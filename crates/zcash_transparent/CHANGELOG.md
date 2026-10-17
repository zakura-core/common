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

- Added the default `pczt` feature, which gates the `pczt` module and
  `builder::TransparentBuilder::build_for_pczt`, and the `bip32` feature, which
  gates the conversions between `keys::TransparentKeyScope` /
  `keys::NonHardenedChildIndex` and `bip32::ChildNumber`
  ([#580](https://github.com/zakura-core/common/pull/580)).

### Changed

- The `bip32` dependency is now optional and the `zcash_script` descriptor
  feature is requested only by `transparent-inputs`, so builds without default
  features and without `transparent-inputs` no longer compile BIP 32. Such
  builds that use the PCZT types or the `ChildNumber` conversions must enable
  `pczt` or `bip32`; `transparent-inputs` now implies `pczt`
  ([#580](https://github.com/zakura-core/common/pull/580)).
- Distinguish an invalid coinbase builder configuration from unexpected transaction inputs.

- Keep wallet derivation APIs enabled by default behind `wallet`; allow verification and direct-address APIs without the external derivation dependency.

## [3.0.0] - 2026-10-13

### Changed

- Updated to stable `bip32` 0.6, `secp256k1` 0.33, and `zcash_script` 0.6 as
  required by the cipher backend migration. `TransparentSignatureContext` no
  longer has lifetime/type parameters; `prepare_transparent_signatures` and
  PCZT input signing/signature methods no longer accept a secp256k1 context
  ([#545](https://github.com/zakura-core/common/pull/545)).
- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

## [2.0.0] - 2026-09-23

### Added

- Added the `zakura-transparent` package as a source-compatible fork of
  `zcash_transparent 0.10.0`, preserving the `zcash_transparent` library target
  and public API ([#471](https://github.com/zakura-core/common/pull/471)).

### Changed

- Renamed the package from `zcash_transparent` to `zakura-transparent`; the
  library target keeps its original name, so existing `use` paths compile
  unchanged.
- Replaced `zcash_protocol` with the `zakura-protocol` package while preserving
  the `zcash_protocol` dependency key and public type paths.
- Raised the minimum supported Rust version from 1.88 to 1.91.

## Record of Fork

`zakura-transparent` began as a fork of the `zcash_transparent` crate and has
been developed independently in this repository since. This changelog starts
at the fork point: history up to that point is documented in the repository
the code was forked from, and this crate's version lineage follows the Zakura
Common workspace rather than continuing the original `0.10.0` numbering.

- Forked from: `zcash_transparent 0.10.0`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`97aefdc3`](https://github.com/zcash/librustzcash/commit/97aefdc39a037da9c4f19a0e8a450d2c7932f53e).
