# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Added `compute_pallas_lagrange_coeffs`, which avoids repeated identity
  checks while extracting coordinates from fixed-base window tables.
- Prepared the `1.0.0-rc.2` release.
- Updated the circuit stack to `ff 0.14`, `group 0.14`, and `rand 0.10`.
- Forked from upstream `halo2_gadgets` and renamed to `zakura-halo2-gadgets`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.5.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
