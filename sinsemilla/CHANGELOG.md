# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Added an unchecked fixed-length, position-weighted hash evaluator that moves
  per-word doublings into a compact reusable generator table. This evaluator
  relies on the discrete-logarithm relation (DLR) assumption to rule out
  Sinsemilla's exceptional incomplete-addition cases; the generic evaluator
  retains exact partial-function semantics.
- Sinsemilla hashing now evaluates each message-word step with an
  algebraically equivalent doubling and mixed addition, avoiding a full
  projective addition while preserving incomplete-addition failures.
- The precomputed Sinsemilla $S$ generators are decoded once and reused across
  hashes instead of validating their coordinates for every message word.
- Sinsemilla hashing now converts messages directly into words instead of
  allocating an intermediate padded bit vector.
- Forked from upstream `sinsemilla` and renamed to `zakura-sinsemilla`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.1.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
