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
