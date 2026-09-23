# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [1.3.0] - 2026-09-23

### Changed

- Sped up base-field subtraction and pairing-based proof verification
  ([#484](https://github.com/zakura-core/common/pull/484)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Added

- Added a `std` cargo feature that enables the `alloc` feature.

### Changed

- Renamed the package from `bls12_381` to `zakura-bls12-381`; the library target
  keeps its original name, so existing `use` paths compile unchanged.
- Updated `ff` and `group` from 0.13 to 0.14 and `rand_core` from 0.6 to 0.10;
  random element generation now goes through the fallible `try_random`
  constructors taking `&mut R` where `R: TryRng + ?Sized` (the infallible
  `random` wrappers remain for `Rng` types), `G1Affine` and `G2Affine` implement
  the new `group::CurveAffine` trait, which takes over the methods of
  `group::prime::PrimeCurveAffine` (a trait they still satisfy through that
  crate's blanket impl), and the `Curve::AffineRepr` associated type is now
  named `Curve::Affine`.
- Replaced the `pairing` dependency with `zakura-pairing` 1.0.0, whose
  `Engine`, `MultiMillerLoop`, and `PairingCurveAffine` traits are implemented
  by this crate's types.
- Updated `digest` from 0.9 to 0.10; hash functions supplied to `ExpandMsgXmd`
  and `ExpandMsgXof` under the `experimental` feature must implement the
  `digest` 0.10 traits, matching `sha2`/`sha3` 0.10.
- Reworked the `experimental` hash-to-curve API to follow
  `draft-irtf-cfrg-hash-to-curve-16`: `hash_to_curve`, `encode_to_curve`, and
  `hash_to_field` now take the message as an iterator of byte chunks that are
  hashed as one concatenated octet string (via the new `Message` trait), so a
  single byte string is passed as `[msg]`; `ExpandMessage` is implemented
  directly by `ExpandMsgXmd` and `ExpandMsgXof`, whose `init_expand` method
  gained a message type parameter and an output-length type parameter; and
  `HashToField` gained a `XofOutputLength` associated type. The points and
  expanded bytes produced for a given input are unchanged.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

### Removed

- Removed the `InitExpandMessage` and `ExpandMessageState` traits from the
  `hash_to_curve` module; their functionality is folded into the reworked
  `ExpandMessage` trait.

### Fixed

- Fixed the `experimental` cargo feature to enable the `groups` feature it
  requires, so building with `--no-default-features --features experimental`
  compiles.
- Fixed `Gt` random sampling to reject the identity element, as the
  `group::Group` random-sampling contract requires.
- Fixed `ExpandMsgXof` to panic when the requested output length exceeds
  `u16::MAX` bytes, instead of silently truncating the length value that is
  hashed into the XOF input.

## Record of Fork

`zakura-bls12-381` began as a fork of the `bls12_381` crate and has been
developed independently in this repository since. This changelog starts at the
fork point: history up to that point is documented in the repository the code
was forked from, and this crate's version lineage restarted at `1.0.0` rather
than continuing the original `0.8.0` numbering.

- Forked from: `bls12_381 0.8.0`, published from
  [zkcrypto/bls12_381](https://github.com/zkcrypto/bls12_381) at commit
  [`7de7b9d9`](https://github.com/zkcrypto/bls12_381/commit/7de7b9d9c509b9973b35a3241b74bbbea95e700a).
- Imported into this repository in commit `fecb02d3d707444b3b9d8aecc052ddbb48598397`.
- The import also ported the crate from the `ff`/`group` 0.13 stack it
  was forked with to `ff`/`group` 0.14.
