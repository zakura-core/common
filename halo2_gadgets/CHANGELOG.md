# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Poseidon, Sinsemilla, and ECC witness generation now use direct small-power,
  doubling, and word-extraction paths instead of generic exponentiation,
  multiplication by two, and intermediate allocations.
- Fixed-base multiplication witness generation now reconstructs window points
  from precomputed interpolation and coordinate constants instead of repeating
  curve arithmetic and batch normalization.
- Prepared the `1.0.0-rc.3` release.
- Prepared the `1.0.0-rc.2` release.
- Updated the circuit stack to `ff 0.14`, `group 0.14`, and `rand 0.10`.
- Forked from upstream `halo2_gadgets` and renamed to `zakura-halo2-gadgets`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.5.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
