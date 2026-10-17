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

- Added the default-enabled `backend-halo2` feature forwarding the Orchard
  backend selection; builds with `--no-default-features` and `orchard` must
  enable it ([#591](https://github.com/zakura-core/common/pull/591)).

### Changed

- Reduced the dependencies enabled by `zcashd-compat` for legacy wallet recovery.
  Legacy seeds produce the same recovery phrases and derived seeds as before
  ([#579](https://github.com/zakura-core/common/pull/579)).
- Keep wallet derivation APIs enabled by default behind `wallet`; allow verification and direct-address APIs without the external derivation dependency.

## [3.0.0] - 2026-10-13

### Changed

- Updated transparent key dependency types to stable `bip32` 0.6 and
  `secp256k1` 0.33. Removed `Key::pubkey_with_context` and
  `Key::der_encode_with_context`; use `Key::pubkey` and `Key::der_encode`
  ([#545](https://github.com/zakura-core/common/pull/545)).
- Add the default-enabled `zip32-addresses` feature for Unified Address
  generation, diversifier-index recovery, gap-address generation, and address
  test generators. Consumers disabling default features must opt in to retain
  these APIs
  ([#552](https://github.com/zakura-core/common/pull/552)).
- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

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
