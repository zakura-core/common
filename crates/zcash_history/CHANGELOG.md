# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

### Added

- Added experimental `zcash_history::{NodeDataV4, V4}` support behind
  `zcash_unstable="nutachyon"`. V4 history nodes commit to the start and end
  Tachyon anchors and the number of transactions containing Tachyon bundles.

### Changed

- Renamed the package from `zcash_history` to `zakura-history`; the library
  target keeps its original name, so existing `use` paths compile unchanged.
- Raised the minimum supported Rust version from 1.88 to 1.91.

## Record of Fork

`zakura-history` began as a fork of the `zcash_history` crate and has been
developed independently in this repository since. This changelog starts at the
fork point: history up to that point is documented in the repository the code
was forked from, and this crate's version lineage restarted at `1.0.0` rather
than continuing the original `0.6.0` numbering.

- Forked from: `zcash_history 0.6.0`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`b74429f9`](https://github.com/zcash/librustzcash/commit/b74429f9e4e3600c27492f1d936fb3b9c818c224).
