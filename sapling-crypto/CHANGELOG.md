# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Prepared the `1.0.0-rc.4` release.
- Replaced `lazy_static` with `once_cell` plus an exactly-once
  initialization wrapper for the lazily-built constant tables.
- The public lazily-initialized constants are now accessor functions:
  `constants::PEDERSEN_HASH_EXP_TABLE` is `constants::pedersen_hash_exp_table()`,
  and the `circuit::constants` generator tables
  (`PROOF_GENERATION_KEY_GENERATOR`, `NOTE_COMMITMENT_RANDOMNESS_GENERATOR`,
  `NULLIFIER_POSITION_GENERATOR`, `VALUE_COMMITMENT_VALUE_GENERATOR`,
  `VALUE_COMMITMENT_RANDOMNESS_GENERATOR`, `SPENDING_KEY_GENERATOR`) are now
  snake_case functions returning `FixedGenerator`.
- Prepared the `1.0.0-rc.3` release.
- Prepared the `1.0.0-rc.2` release.
- Updated to `ff 0.14`, `group 0.14`, `rand 0.10`, and the Zakura Groth16 and
  Jubjub forks.
- Forked from upstream `sapling-crypto` and renamed to `zakura-sapling-crypto`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.7.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.

### Added

- Opt-in `fused-pedersen` feature, which caches fused chunk-block lookup tables
  (about 6.2 MiB) to speed up non-circuit Pedersen hashing. The default remains
  the original 8-bit exp-window tables.
