# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

Initial development of the crate. It has no released version yet, and it
is not a fork: the code is original to this repository.

- Added the `pipeline` module — a GPU-shaped Pasta multiscalar
  multiplication (GLV split, signed digits, bucket sort, bucket
  accumulation, chunked bucket reduction, Horner combination) with a CPU
  `Reference` backend, and the `field` and `curve` modules holding the portable
  arithmetic that the Metal kernels mirror: twenty 13-bit limbs with a
  carry-free Montgomery multiplication in 32-bit integer arithmetic.
- Added the `Accelerator` wrapper implementing
  `pasta_curves::glv::accelerator::MultiexpAccelerator` over any backend,
  with `install` (Metal, Apple AArch64 only) and `install_reference`.
- Added the `metal` module on Apple AArch64 targets: a dependency-free
  Objective-C bridge and the Metal compute backend, compiling the bundled
  `SHADER_SOURCE` at runtime. The backend is unbenchmarked; the default
  `Config::min_terms` is a placeholder.

## Record of Fork

`zakura-pasta-msm-metal` is not a fork: it was written for this repository,
alongside the accelerator registry it plugs into in `zakura-pasta-curves`.
There is no upstream crate whose history precedes this changelog.
