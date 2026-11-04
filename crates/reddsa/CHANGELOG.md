# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [5.1.0] - 2026-11-03

### Added

- Added `From<jubjub::ExtendedPoint>` for
  `VerificationKey<sapling::Binding>` to retain an existing valid point and
  derive its canonical encoding without decoding it again
  ([#675](https://github.com/zakura-core/common/pull/675)).
- Added `batch::Item::from_binding_key` to retain a binding verification key's
  point through batch and fallback verification instead of decoding it again
  ([#675](https://github.com/zakura-core/common/pull/675)).
- Added `From<pasta_curves::pallas::Point>` for
  `VerificationKey<orchard::Binding>` with `pallas-pasta`, retaining a valid
  native point and its canonical encoding with a debug round-trip assertion
  ([#676](https://github.com/zakura-core/common/pull/676)).
- Added `batch::Item::from_spendauth_key` with `alloc` to retain an existing
  spend authorization verification key through batch and fallback verification
  ([#676](https://github.com/zakura-core/common/pull/676)).
- Added `From<VerificationKey<sapling::SpendAuth>> for jubjub::AffinePoint`
  to normalize a stored spend authorization point without decoding its bytes
  ([#677](https://github.com/zakura-core/common/pull/677)).

### Changed

- Corrected verification-key documentation to reflect the existing acceptance
  of identity and other small-order keys during byte decoding
  ([#675](https://github.com/zakura-core/common/pull/675)).

## [5.0.0] - 2026-11-02

### Added

- Added the `pallas-sensei` feature selecting the native Pallas
  implementation; select at most one of `pallas-pasta` (the default) and
  `pallas-sensei`
  ([#624](https://github.com/zakura-core/common/pull/624)).

### Changed

- Sped up RedDSA batch verification by giving one signature in each batch
  weight 1 instead of a random weight
  ([#667](https://github.com/zakura-core/common/pull/667)).

## [4.0.0] - 2026-10-20

### Added

- Added the default-enabled `pallas-pasta` feature gating the Pallas
  signature implementation; builds without it retain Jubjub support and drop
  the `pasta_curves` dependency
  ([#591](https://github.com/zakura-core/common/pull/591)).

## [3.0.0] - 2026-10-13

### Changed

- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

### Removed

- Removed the `frost` feature and `reddsa::frost` module, along with the
  `frost-rerandomized` and `rand_core_06` features that only enabled its
  dependencies. FROST users must depend on `zakura-reddsa-frost` and import
  `reddsa_frost::{redjubjub, redpallas}` instead
  ([#544](https://github.com/zakura-core/common/pull/544)).

## [2.1.0] - 2026-09-29

### Changed

- Sped up Sapling single signature verification by about 36% when the `alloc`
  feature is enabled ([#480](https://github.com/zakura-core/common/pull/480)).
- Sped up empty and single-item signature batch verification. These batches
  no longer consume random bytes
  ([#498](https://github.com/zakura-core/common/pull/498)).

## [2.0.0] - 2026-09-23

### Changed

- Sped up Sapling batch signature verification by about 14–17% for batches
  of 8–64 signatures ([#481](https://github.com/zakura-core/common/pull/481)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Changed

- Renamed the package from `reddsa` to `zakura-reddsa`; the library target keeps
  its upstream name, so existing `use` paths compile unchanged.
- Updated `group` from 0.13 to 0.14 and `rand_core` from 0.6 to 0.10;
  `SigningKey::new`, `SigningKey::sign`, and `batch::Verifier::verify` now bound
  their RNG arguments on `rand_core` 0.10's `Rng + CryptoRng` traits.
- Replaced the `jubjub` dependency with `zakura-jubjub` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `pasta_curves` dependency with `zakura-pasta-curves` 1.0.0,
  whose types appear in this crate's API.
- Kept the FROST modules (`frost::redjubjub` and `frost::redpallas`) on
  `rand_core` 0.6: their APIs still accept `rand_core` 0.6 RNGs, and the
  re-exported `rand_core` now includes `OsRng` because the `frost` feature
  enables its `getrandom` feature.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-reddsa` began as a fork of the `reddsa` crate and has been developed
independently in this repository since. This changelog starts at the fork
point: history up to that point is documented in the repository the code was
forked from, and this crate's version lineage restarted at `1.0.0` rather than
continuing the original `0.5.2` numbering.

- Forked from: `reddsa 0.5.2`, published from
  [ZcashFoundation/reddsa](https://github.com/ZcashFoundation/reddsa) at commit
  [`3792daa9`](https://github.com/ZcashFoundation/reddsa/commit/3792daa95e588c1af6bd4805105bfb6ea7e9ad49).
- Imported into this repository in commit `a57d014096a67071a2c6522a160c7e0dfbeff0f4`.
