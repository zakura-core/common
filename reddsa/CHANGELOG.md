# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Single-signature verification now computes `s·B − c·A` as one variable-time
  double-scalar multiplication instead of two constant-time full-width
  multiplications (all inputs are public). With the `alloc` feature this uses
  the GLV endomorphism on Pallas (RedPallas) and the existing wNAF Straus
  ladder on Jubjub (RedJubjub); without `alloc` the previous code is kept.
- RedPallas multiscalar multiplication (used by batch verification) now uses
  GLV-split scalars on one shared doubling ladder
  (`pasta_curves::glv::sum_of_products_vartime`) for sums of up to 32 terms,
  where halving the doublings wins; larger sums keep the width-5 wNAF Straus
  ladder, whose sparser digits win once additions dominate (measured crossover
  on both benchmark architectures). The `alloc` feature now enables
  `pasta_curves/glv`.
- Prepared the `1.0.0-rc.2` release.
- Updated to `group 0.14` and the Zakura Pasta and Jubjub forks, while retaining
  the `rand_core 0.6` boundary required by FROST.
- Forked from upstream `reddsa` and renamed to `zakura-reddsa`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.5.2); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
