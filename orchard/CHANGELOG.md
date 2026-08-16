# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Batched trial decryption now interleaves pairs of GLV key-agreement
  ladders. This preserves shared-secret bytes, invalid-lane ordering, and the
  existing wNAF fallback. The path remains variable-time in the
  privacy-sensitive, wallet-local incoming viewing key; pairing does not make
  it constant-time.
- Forked from upstream `orchard` and renamed to `zakura-orchard`; this
  changelog starts fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited
  upstream version (0.15.5); the initial Zakura release will be preceded by
  `1.0.0-rc` release candidates.
