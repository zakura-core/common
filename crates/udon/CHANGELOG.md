# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [0.3.0] - 2026-11-10

### Added

- Added `Point::batch_from_bytes`, decoding batches of compressed point
  encodings with interleaved square-root chains while accepting and rejecting
  exactly what `Point::from_bytes` does
  ([#725](https://github.com/zakura-core/common/pull/725)).

## [0.2.0] - 2026-11-01

### Added

- Enabled crates.io publication of Pasta field and curve arithmetic and
  allocation-free FFTs ([#624](https://github.com/zakura-core/common/pull/624)).
- Added the `Alpha`, `AlphaPrepared`, `Odd`, and `OddPrepared` table variants
  to the exhaustive `msm::Bases` enum; the crate version becomes `0.2.0`
  because exhaustive matches on the published `0.1.0` surface must handle them
  ([#624](https://github.com/zakura-core/common/pull/624)).

### Changed

- Select x86-64 assembly at build time with BMI2 and ADX compiler target
  features or the explicit assembly feature. Baseline builds use portable
  Rust, and the portable override retains precedence
  ([#661](https://github.com/zakura-core/common/pull/661)).

## Record of Fork

`zakura-udon` is an original implementation imported into the Zakura
Common workspace in commit
[`97620e86`](https://github.com/zakura-core/common/commit/97620e86).
It retains an independent package version, initially `0.1.0`.
