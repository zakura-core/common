# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Removed the unused `bls12_381` and `tracing` dependencies (`bls12_381`
  was previously pulled into builds that did not enable the `sapling`
  feature), and moved `group` (doc examples only) to dev-dependencies.

- Prepared the `1.0.0-rc.3` release.
- Prepared the `1.0.0-rc.2` release.
- Replaced the upstream BLS12-381 and Jubjub dependencies with the Zakura
  `ff 0.14`-compatible forks.
- Forked from upstream `zcash_keys` and renamed to `zakura-keys`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.16.1); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
