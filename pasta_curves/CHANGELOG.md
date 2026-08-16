# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Added `glv::Table::mul_decomposed_pair`, for interleaving two independent
  GLV ladders that use the same decomposed scalar. Batched same-scalar GLV
  multiplication now uses it to interleave pairs.
- Forked from upstream `pasta_curves` and renamed to
  `zakura-pasta-curves`; this changelog starts fresh for the Zakura fork's
  initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited
  upstream version (0.5.2); the initial Zakura release will be preceded by
  `1.0.0-rc` release candidates.
