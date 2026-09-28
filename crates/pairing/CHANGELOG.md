# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [2.1.0-rc.0] - 2026-09-27

### Added

- Added defaulted `Engine::g1_to_affine_vartime` and
  `Engine::g2_to_affine_vartime` hooks for explicit affine conversion with
  possible input-dependent timing
  ([#494](https://github.com/zakura-core/common/pull/494)).
- Added `MultiMillerLoop::prepare_reusable_g2` for engines that can spend more
  preparation time to speed up repeated Miller loops
  ([#495](https://github.com/zakura-core/common/pull/495)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `pairing` to `zakura-pairing`; the library target
  keeps its original name, so existing `use` paths compile unchanged.
- Updated `group` from 0.13 to 0.14 (moving the re-exported `ff` traits from
  0.13 to 0.14 and `rand_core` from 0.6 to 0.10); the `pub use group` re-export
  and the trait bounds on `Engine`, `PairingCurveAffine`, `MultiMillerLoop`, and
  `MillerLoopResult` now require implementations from that stack.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-pairing` began as a fork of the `pairing` crate and has been developed
independently in this repository since. This changelog starts at the fork
point: history up to that point is documented in the repository the code was
forked from, and this crate's version lineage restarted at `1.0.0` rather than
continuing the original `0.23.0` numbering.

- Forked from: `pairing 0.23.0`, published from
  [zkcrypto/pairing](https://github.com/zkcrypto/pairing) at commit
  [`11eff5b3`](https://github.com/zkcrypto/pairing/commit/11eff5b3680a08b09c61cbe75eaa803a1e85d80b).
- Imported into this repository in commit `295ad3fb0f7a8dd5c9ac781dd9b5a05a5eac8473`.
- The import also ported the crate from the `ff`/`group` 0.13 stack it
  was forked with to `ff`/`group` 0.14.
