# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

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
