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

- Added network-aware block spacing and anchor grids for ZIP 318, preserving reference durations across NU7 activation ([#593](https://github.com/zakura-core/common/pull/593)).
- Added named NU7 block limits for Sapling spends and outputs, Orchard-family actions, and the combined shielded budget ([#598](https://github.com/zakura-core/common/pull/598)).

### Changed

- Scaled ZIP 318 anchor boundaries and rolling expiry by the NU7 spacing ratio. Pool-migration constants and the expiry function now require block spacing, and boundary methods belong to the anchor grid ([#593](https://github.com/zakura-core/common/pull/593)).
- Set the NU7 activation height for Mainnet to 3543405: `MAIN_NETWORK` now
  returns `Some(3543405)` from `activation_height(NetworkUpgrade::Nu7)` and
  selects `BranchId::Nu7` from that height onward
  ([#616](https://github.com/zakura-core/common/pull/616)).

### Removed

- Removed `memuse::DynamicUsage` implementations for `TxId`, `BlockHeight`, `TxIndex`, `ZatBalance` and the network and upgrade types, together with the `memuse` dependency. Code that measured these types with `dynamic_usage()` no longer compiles
  ([#589](https://github.com/zakura-core/common/pull/589)).

## [3.0.0] - 2026-10-13

### Added

- Added `zcash_protocol::encoding` with `MAX_COMPACT_SIZE`, `CompactSize`,
  `Vector`, `Array`, `Optional`, and `ReverseHex`, preserving the
  `zcash_encoding 0.4.0` API and serialization behavior, including writing
  values above the reader's maximum
  ([#540](https://github.com/zakura-core/common/pull/540)).

### Changed

- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

## [2.2.0] - 2026-09-30

### Changed

- Set the NU7 activation height for Testnet to 4465026: `TEST_NETWORK` now
  returns `Some(4465026)` from `activation_height(NetworkUpgrade::Nu7)` and
  selects `BranchId::Nu7` from that height onward. The Mainnet activation
  height remains unscheduled
  ([#534](https://github.com/zakura-core/common/pull/534)).

## [2.0.0] - 2026-09-23

### Added

- Added the `zakura-protocol` package as a source-compatible fork of
  `zcash_protocol 0.10.5`, preserving the `zcash_protocol` library target and
  public API ([#471](https://github.com/zakura-core/common/pull/471)).
- Exposed NU7 and consensus branch ID `0x77190AD9` without requiring the
  `zcash_unstable="nu7"` configuration flag; predefined Mainnet and Testnet
  parameters remain unscheduled
  ([#474](https://github.com/zakura-core/common/pull/474),
  [#492](https://github.com/zakura-core/common/pull/492)).

### Changed

- Renamed the package from `zcash_protocol` to `zakura-protocol`; the library
  target keeps its original name, so existing `use` paths compile unchanged.
- Raised the minimum supported Rust version from 1.88 to 1.91.

### Fixed

- Made local consensus epoch bounds follow the next configured activation,
  including partial upgrade schedules
  ([#474](https://github.com/zakura-core/common/pull/474)).

## Record of Fork

`zakura-protocol` began as a fork of the `zcash_protocol` crate and has been
developed independently in this repository since. This changelog starts at the
fork point: history up to that point is documented in the repository the code
was forked from, and this crate's version lineage follows the Zakura Common
workspace rather than continuing the original `0.10.5` numbering.

- Forked from: `zcash_protocol 0.10.5`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`97aefdc3`](https://github.com/zcash/librustzcash/commit/97aefdc39a037da9c4f19a0e8a450d2c7932f53e).
- Imported into this repository in commit `80583d0e88b8550b621c59fd1c2db8bf8c1d7e79`.
