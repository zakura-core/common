# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Batch trial-decryption key agreement now multiplies all of a batch's prepared
  ephemeral keys by each viewing key in one synchronized GLV call, picking up the
  batched-inversion affine ladder in `pasta_curves` for large scans. Trial
  decryption of undecryptable outputs (the wallet-scanning hot case) is about 9%
  faster end to end from the accompanying `pasta_curves` recoding change.
- Added reproducible one-Action prover and validated-corpus batch-verifier
  benchmark harnesses.
- The Sinsemilla note-commitment domain is now initialized once and reused
  instead of deriving the same generators for every commitment.
- Forked from upstream `orchard` and renamed to `zakura-orchard`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.15.5); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
