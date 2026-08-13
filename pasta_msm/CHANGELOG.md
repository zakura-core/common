# Changelog

All notable changes to `zakura-pasta-msm` will be documented in this file.

## [Unreleased]

### Changed

- Changed the native backend to use checked GLV scalar decomposition before
  signed-Booth Pippenger, with an unsplit fallback if validation fails.

### Added

- Added the `pallas_vartime` and `vesta_vartime` caller-thread CPU
  multiscalar-multiplication functions.
- The Cargo package is named `zakura-pasta-msm` while retaining the
  `pasta_msm` Rust library name.
