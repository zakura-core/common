# Changelog

All notable changes to this library will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this library adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [2.0.0] - 2026-09-23

### Added

- Added the `zakura-zip321` package as a source-compatible fork of
  `zip321 0.9.0`, preserving the `zip321` library target and public API
  ([#471](https://github.com/zakura-core/common/pull/471)).

### Changed

- Renamed the package from `zip321` to `zakura-zip321`; the library target
  keeps its original name, so existing `use` paths compile unchanged.
- Replaced `zcash_address` and `zcash_protocol` with their Zakura packages
  while preserving the dependency keys and public type paths.
- Raised the minimum supported Rust version from 1.88 to 1.91.

## Record of Fork

`zakura-zip321` began as a fork of the `zip321` crate and has been developed
independently in this repository since. This changelog starts at the fork
point: history up to that point is documented in the repository the code was
forked from, and this crate's version lineage follows the Zakura Common
workspace rather than continuing the original `0.9.0` numbering.

- Forked from: `zip321 0.9.0`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`97aefdc3`](https://github.com/zcash/librustzcash/commit/97aefdc39a037da9c4f19a0e8a450d2c7932f53e).
