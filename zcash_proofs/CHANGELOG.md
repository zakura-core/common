# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Removed `local-prover` from the default feature set; the default features
  are now just `multicore`. Consumers that locate the Sapling parameters on
  disk (`~/.zcash-params` discovery via the `directories` machinery) must now
  enable the `local-prover` (or `directories`/`download-params`) feature
  explicitly. Consumers using `bundled-prover` are unaffected.
- Prepared the `1.0.0-rc.3` release.
- Prepared the `1.0.0-rc.2` release.
- Replaced the upstream Bellman, BLS12-381, and Jubjub dependencies with the
  Zakura `ff 0.14`-compatible forks.
- Forked from upstream `zcash_proofs` and renamed to `zakura-proofs`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.30.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
