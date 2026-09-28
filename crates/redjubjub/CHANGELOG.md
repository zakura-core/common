# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [2.1.0-rc.0] - 2026-09-27

### Changed

- Sped up empty and single-item batch RedJubjub verification through the
  updated RedDSA verifier
  ([#498](https://github.com/zakura-core/common/pull/498)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `redjubjub` to `zakura-redjubjub`; the library target
  keeps its original name, so existing `use` paths compile unchanged.
- Replaced the `reddsa` dependency with `zakura-reddsa` 1.0.0, whose types
  appear in this crate's API.
- Updated `rand_core` from 0.6 to 0.10; the RNG parameters of `SigningKey::new`,
  `SigningKey::sign`, and `batch::Verifier::verify` are now bounded by `Rng +
  CryptoRng` instead of `RngCore + CryptoRng`.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-redjubjub` began as a fork of the `redjubjub` crate and has been
developed independently in this repository since. This changelog starts at the
fork point: history up to that point is documented in the repository the code
was forked from, and this crate's version lineage restarted at `1.0.0` rather
than continuing the original `0.8.0` numbering.

- Forked from: `redjubjub 0.8.0`, published from
  [ZcashFoundation/redjubjub](https://github.com/ZcashFoundation/redjubjub) at commit
  [`2f618e9b`](https://github.com/ZcashFoundation/redjubjub/commit/2f618e9b47617ae9d4112913391a5c3fbb8106f0).
- Imported into this repository in commit `a57d014096a67071a2c6522a160c7e0dfbeff0f4`.
