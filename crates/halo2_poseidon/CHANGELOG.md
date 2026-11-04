# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [5.0.0] - 2026-11-02

### Changed

- Removed the `bitvec` dependency ([#626](https://github.com/zakura-core/common/pull/626)).

## [3.0.0] - 2026-10-13

### Changed

- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `halo2_poseidon` to `zakura-halo2-poseidon`; the
  library target keeps its original name, so existing `use` paths compile
  unchanged.
- Updated `ff` and `group` from 0.13 to 0.14; the `Field` trait bounds on
  `Spec`, `Domain`, `Hash`, and the sponge APIs now refer to the 0.14 traits.
- Replaced the `pasta_curves` dependency with `zakura-pasta-curves` 1.0.0,
  whose types appear in this crate's API.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-halo2-poseidon` began as a fork of the `halo2_poseidon` crate and has
been developed independently in this repository since. This changelog starts
at the fork point: history up to that point is documented in the repository
the code was forked from, and this crate's version lineage restarted at
`1.0.0` rather than continuing the original `0.1.0` numbering.

- Forked from: `halo2_poseidon 0.1.0`, published from
  [zcash/halo2](https://github.com/zcash/halo2) at commit
  [`f066ace1`](https://github.com/zcash/halo2/commit/f066ace1f234d7fe1908851ed86b1801e0b1ffea).
- Imported into this repository in commit `16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b`.
