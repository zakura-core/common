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

- Replaced the `zcash_address 0.13`, `zcash_protocol 0.10`, and
  `zcash_transparent 0.10` dependencies with `zakura-address`,
  `zakura-protocol`, and `zakura-transparent` 2.0.0, whose types appear in
  this crate's API ([#471](https://github.com/zakura-core/common/pull/471)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `zcash_keys` to `zakura-keys`; the library target
  keeps its original name, so existing `use` paths compile unchanged.
- Replaced the `orchard` dependency with `zakura-orchard` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `sapling-crypto` dependency with `zakura-sapling-crypto` 1.0.0,
  whose types appear in this crate's API.
- Raised the minimum supported Rust version from 1.88 to 1.91.

## Record of Fork

`zakura-keys` began as a fork of the `zcash_keys` crate and has been developed
independently in this repository since. This changelog starts at the fork
point: history up to that point is documented in the repository the code was
forked from, and this crate's version lineage restarted at `1.0.0` rather than
continuing the original `0.16.1` numbering.

- Forked from: `zcash_keys 0.16.1`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`cb356a7d`](https://github.com/zcash/librustzcash/commit/cb356a7def26d0bd8e1f21709951aeea137f58fa).
- Imported into this repository in commit `16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b`.
