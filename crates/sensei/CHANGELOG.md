# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [0.1.2] - 2026-11-10

### Changed

- Sped up batch verification: proof points decode together ahead of transcript
  reading, instance commitments walk doubling-free fixed-base tables (about
  245 KiB prepared at warmup) with a bundle's shared anchor term computed once,
  and RedPallas batch verification decodes its points together and runs its
  equation on the worker pool for larger batches
  ([#725](https://github.com/zakura-core/common/pull/725)).

## [0.1.1] - 2026-11-04

### Added

- Added `redpallas::SigningKey::negate` and
  `redpallas::SigningKey::randomize_with_verification_key`, which reuse the
  stored verification key instead of recomputing it
  ([#680](https://github.com/zakura-core/common/pull/680)).

## [0.1.0] - 2026-10-31

### Added

- Enabled crates.io publication of native Orchard primitives, Ironwood proving,
  and historical proof verification
  ([#624](https://github.com/zakura-core/common/pull/624)).

### Changed

- Removed `Fp::to_le_bits` and `Fq::to_le_bits`; read the canonical
  little-endian bits from `to_bytes` instead. The crate no longer depends on
  `bitvec` ([#637](https://github.com/zakura-core/common/pull/637)).

## Record of Fork

`zakura-sensei` is an original implementation imported into the Zakura
Common workspace in commit
[`5d4d6b82`](https://github.com/zakura-core/common/commit/5d4d6b82).
It retains an independent package version, initially `0.1.0`.
