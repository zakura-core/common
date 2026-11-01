# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [5.0.0-rc.1] - 2026-10-31

### Changed

- Removed `bits` from the default features; enable it explicitly for the
  `PrimeFieldBits` implementation. The crate no longer depends on `bitvec`
  ([#626](https://github.com/zakura-core/common/pull/626)).

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

- Renamed the package from `jubjub` to `zakura-jubjub`; the library target keeps
  its upstream name, so existing `use` paths compile unchanged.
- Replaced the `bls12_381` dependency with `zakura-bls12-381` 1.0.0, whose
  types appear in this crate's API.
- Updated `ff` and `group` from 0.13 to 0.14 and `rand_core` from 0.6 to 0.10;
  random sampling now goes through the fallible `try_random` methods over
  `rand_core::TryRng` (with the infallible `random` retained as a provided
  method), `AffinePoint`'s constructors and conversions now come from the new
  `group::CurveAffine` trait rather than `CofactorCurveAffine` (which it still
  satisfies through that crate's blanket implementation), and the `Curve`
  implementation's affine associated type is now named `Affine` instead of
  `AffineRepr`.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-jubjub` began as a fork of the `jubjub` crate and has been developed
independently in this repository since. This changelog starts at the fork
point: history up to that point is documented in the repository the code was
forked from, and this crate's version lineage restarted at `1.0.0` rather than
continuing the original `0.10.0` numbering.

- Forked from: `jubjub 0.10.0`, published from
  [zkcrypto/jubjub](https://github.com/zkcrypto/jubjub) at commit
  [`47dfe518`](https://github.com/zkcrypto/jubjub/commit/47dfe5181ccf39166c0c479c35c0644d708f4294).
- Imported into this repository in commit `8021245781a7099c89d8a4650c20e3ab14578fe5`.
- The import also ported the crate from the `ff`/`group` 0.13 stack it
  was forked with to `ff`/`group` 0.14.
