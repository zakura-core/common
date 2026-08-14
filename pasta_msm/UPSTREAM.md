# Upstream provenance

This crate is an attributed Apache-2.0 derivative, not a clean-room rewrite.
All upstream links below name immutable commit blobs.

The local Cargo package is `zakura-pasta-msm`, while its Rust library name is
`pasta_msm`. References to `pasta-msm` below identify Supranational's upstream
project.

## Revisions

- Semolina 0.1.4:
  [`13ffc78074a6fbec44a4fd12b7f585a0bc1dc154`][semolina]
- Sppark:
  [`17278d74295392f9813f009300b257a688422b7a`][sppark]
- `pasta-msm`:
  [`861357baceec7690a3a85631a9d5eba9f08076ed`][pasta-msm]
- Zcash `pasta_curves`:
  [`f76fecb533003e525160e7e6d299b955a9d78cc4`][zcash-pasta]

[semolina]: https://github.com/supranational/semolina/tree/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154
[sppark]: https://github.com/supranational/sppark/tree/17278d74295392f9813f009300b257a688422b7a
[pasta-msm]: https://github.com/supranational/pasta-msm/tree/861357baceec7690a3a85631a9d5eba9f08076ed
[zcash-pasta]: https://github.com/zcash/pasta_curves/tree/f76fecb533003e525160e7e6d299b955a9d78cc4

## Zakura-authored package boundary

| Local file | Upstream reference | Modification |
| --- | --- | --- |
| `Cargo.toml` | `pasta-msm` [`Cargo.toml`][pm-manifest] | Renamed the package to `zakura-pasta-msm` while retaining the `pasta_msm` Rust library name; replaced the standalone package graph with one exact workspace `pasta_curves` dependency and `cc`; removed every feature and CUDA, Semolina, Sppark, `which`, Rayon, and benchmark dependency. |
| `build.rs` | Semolina [`build.rs`][sem-build] and `pasta-msm` [`build.rs`][pm-build] | Uses Cargo target variables to select checked-in CPU assembly and define release assertion behavior. Baseline x86_64 builds compile both field backends for one-time runtime selection; explicit ADX and non-x86_64 builds compile one direct backend. It performs no host probing, CUDA discovery, or external include-path lookup. |
| `build_selection.rs` | None | New private target-feature, runtime-dispatch, and MSVC assembly-source selection shared by the build script and its regression test. |
| `src/lib.rs` | `pasta-msm` [`src/lib.rs`][pm-lib] | Renamed the two functions to make variable-time behavior explicit; added empty-input handling and kept only the typed safe API. |
| `src/ffi.rs` | `pasta-msm` [`src/lib.rs`][pm-lib] | New private FFI layer with compile-time layout checks, status handling, and documented unsafe blocks. |
| `tests/build_selection.rs` | None | Includes the private build selector to verify that MSVC baseline x86_64 builds include both checked-in multiplication backends, while explicit ADX and AArch64 targets keep one backend. |
| `tests/differential.rs` | `pasta-msm` [`src/tests.rs`][pm-tests] and Zcash `pasta_curves` [`src/glv.rs`][zcash-glv], [`sage/glv_boundary_scalars.sage`][zcash-glv-boundaries] | Replaced the upstream fixtures with deterministic two-curve differential cases covering empty inputs, signed-window and checked Babai boundaries, randomized inputs, identities, zero scalars, and Orchard-sized inputs. |
| `tests/concurrency.rs` | `pasta-msm` [`src/tests.rs`][pm-tests] | Added independent concurrent calls to enforce the removal of shared native state. |
| `native/msm.cpp` | `pasta-msm` [`src/pippenger.cpp`][pm-bridge] | Removed CUDA and the global thread pool; added status-returning, `noexcept` entrypoints with catch-all exception containment; delegates privately to the checked GLV backend. It can be instantiated as the two public bridge entrypoints or as a uniquely named private baseline/ADX backend. |
| `native/msm_baseline.cpp` | `native/msm.cpp` above | New Zakura-authored wrapper that instantiates the private baseline MSM backend with a unique field type and private symbols. |
| `native/msm_adx.cpp` | `native/msm.cpp` above | New Zakura-authored wrapper that instantiates the private BMI2/ADX MSM backend with a unique field type and private symbols. |
| `native/runtime_dispatch.cpp` | None | New Zakura-authored x86_64 dispatcher. It checks CPUID leaf 7 once using C++11 thread-safe static initialization and selects the private BMI2/ADX backend only when both required feature bits are present. The existing two public C entrypoints and their signatures are unchanged. |
| `native/semolina/pasta_baseline.c` | Semolina [`src/pasta.c`][sem-pasta-c] | New Zakura-authored wrapper that instantiates the pinned Semolina C source with private baseline symbol names. |
| `native/semolina/pasta_adx.c` | Semolina [`src/pasta.c`][sem-pasta-c] | New Zakura-authored wrapper that instantiates the pinned Semolina C source with private BMI2/ADX symbol names. |
| `native/asm/regenerate.sh` | Semolina [`src/refresh.sh`][sem-refresh] | Regenerates every checked-in target in one pass, adds attribution notices, and supports clean-diff verification. |
| `LICENSE-APACHE` | `pasta-msm` [`LICENSE`][pm-license] | Renamed only. |

[pm-manifest]: https://github.com/supranational/pasta-msm/blob/861357baceec7690a3a85631a9d5eba9f08076ed/Cargo.toml
[sem-build]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/build.rs
[pm-build]: https://github.com/supranational/pasta-msm/blob/861357baceec7690a3a85631a9d5eba9f08076ed/build.rs
[pm-lib]: https://github.com/supranational/pasta-msm/blob/861357baceec7690a3a85631a9d5eba9f08076ed/src/lib.rs
[pm-tests]: https://github.com/supranational/pasta-msm/blob/861357baceec7690a3a85631a9d5eba9f08076ed/src/tests.rs
[pm-bridge]: https://github.com/supranational/pasta-msm/blob/861357baceec7690a3a85631a9d5eba9f08076ed/src/pippenger.cpp
[sem-refresh]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/refresh.sh
[pm-license]: https://github.com/supranational/pasta-msm/blob/861357baceec7690a3a85631a9d5eba9f08076ed/LICENSE

## Zcash `pasta_curves`-derived file

`native/glv.hpp` is derived under the Apache-2.0 option from Zcash
`pasta_curves` [`src/glv.rs`][zcash-glv], including the short lattice basis,
Babai coefficients, checked rounding and signed-half bounds, and Pasta
endomorphism. Zakura translated the Rust limb arithmetic to private C++,
added bulk Montgomery-to-canonical conversion, wired the split into the
caller-thread signed-Booth backend, and falls back to the unsplit signed MSM
in release builds if any validation fails. It intentionally carries Zcash,
not Supranational, attribution.

The exact Babai boundary witnesses in `tests/differential.rs` are derived from
[`sage/glv_boundary_scalars.sage`][zcash-glv-boundaries]. The constants in the
implementation were generated by
[`sage/glv_constants.sage`][zcash-glv-constants] and are independently checked
by the pinned `src/glv.rs` tests.

[zcash-glv]: https://github.com/zcash/pasta_curves/blob/f76fecb533003e525160e7e6d299b955a9d78cc4/src/glv.rs
[zcash-glv-boundaries]: https://github.com/zcash/pasta_curves/blob/f76fecb533003e525160e7e6d299b955a9d78cc4/sage/glv_boundary_scalars.sage
[zcash-glv-constants]: https://github.com/zcash/pasta_curves/blob/f76fecb533003e525160e7e6d299b955a9d78cc4/sage/glv_constants.sage

## Sppark-derived files

| Local file | Exact upstream blob(s) | Modification |
| --- | --- | --- |
| `native/sppark/pasta.hpp` | [`ff/pasta.hpp`][sppark-pasta] | Retained only the host Pasta type include; removed every CUDA and HIP definition. |
| `native/sppark/curve.hpp` | [`ec/affine_t.hpp`][sppark-affine], [`ec/xyzz_t.hpp`][sppark-xyzz] | Retained the affine and XYZZ CPU formulas needed by Pippenger; removed device representations, GPU formulas, and unused coordinate operations. |
| `native/sppark/pippenger.hpp` | [`msm/pippenger.hpp`][sppark-pippenger] | Retained the serial Pippenger structure, added the tested signed-Booth recoding and a header-private raw-canonical-scalar entry for GLV, and removed unsigned, GPU, and native-thread-pool paths. |

[sppark-pasta]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/ff/pasta.hpp
[sppark-affine]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/ec/affine_t.hpp
[sppark-xyzz]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/ec/xyzz_t.hpp
[sppark-pippenger]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/msm/pippenger.hpp

## Semolina-derived source and generator files

Every file in this table retains its upstream copyright and SPDX header and
adds a `Modified by Zakura` notice. The arithmetic source and generator bodies
are otherwise unchanged apart from whitespace normalization. `assembly.S`
can include both x86_64 multiplication backends for runtime dispatch, while
`vect.h` drops its unused CUDA limb definition and CUDA-specific compiler
guard and can rename the private C wrapper symbols.

| Local path below `native/semolina/` | Exact Semolina blob |
| --- | --- |
| `assembly.S` | [`src/assembly.S`][sem-assembly] |
| `bytes.h` | [`src/bytes.h`][sem-bytes] |
| `consts.c` | [`src/consts.c`][sem-consts] |
| `pasta.c` | [`src/pasta.c`][sem-pasta-c] |
| `pasta_t.hpp` | [`src/pasta_t.hpp`][sem-pasta-hpp] |
| `recip.c` | [`src/recip.c`][sem-recip] |
| `vect.h` | [`src/vect.h`][sem-vect] |
| `asm/arm-xlate.pl` | [`src/asm/arm-xlate.pl`][sem-arm-xlate] |
| `asm/ct_inverse_mod_256-armv8.pl` | [`src/asm/ct_inverse_mod_256-armv8.pl`][sem-inv-arm] |
| `asm/ct_inverse_mod_256-x86_64.pl` | [`src/asm/ct_inverse_mod_256-x86_64.pl`][sem-inv-x86] |
| `asm/pasta_add-armv8.pl` | [`src/asm/pasta_add-armv8.pl`][sem-add-arm] |
| `asm/pasta_add-x86_64.pl` | [`src/asm/pasta_add-x86_64.pl`][sem-add-x86] |
| `asm/pasta_mul-armv8.pl` | [`src/asm/pasta_mul-armv8.pl`][sem-mul-arm] |
| `asm/pasta_mulq-x86_64.pl` | [`src/asm/pasta_mulq-x86_64.pl`][sem-mulq-x86] |
| `asm/pasta_mulx-x86_64.pl` | [`src/asm/pasta_mulx-x86_64.pl`][sem-mulx-x86] |
| `asm/x86_64-xlate.pl` | [`src/asm/x86_64-xlate.pl`][sem-x86-xlate] |

[sem-assembly]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/assembly.S
[sem-bytes]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/bytes.h
[sem-consts]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/consts.c
[sem-pasta-c]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/pasta.c
[sem-pasta-hpp]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/pasta_t.hpp
[sem-recip]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/recip.c
[sem-vect]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/vect.h
[sem-arm-xlate]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/arm-xlate.pl
[sem-inv-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/ct_inverse_mod_256-armv8.pl
[sem-inv-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/ct_inverse_mod_256-x86_64.pl
[sem-add-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/pasta_add-armv8.pl
[sem-add-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/pasta_add-x86_64.pl
[sem-mul-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/pasta_mul-armv8.pl
[sem-mulq-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/pasta_mulq-x86_64.pl
[sem-mulx-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/pasta_mulx-x86_64.pl
[sem-x86-xlate]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/asm/x86_64-xlate.pl

## Generated assembly files

The following files correspond one-for-one with the same exact paths under
Semolina's `src/` directory at the pinned revision. Zakura's regeneration
script prepends the copyright, SPDX, and modification notice and normalizes
trailing whitespace; the generated instructions are unchanged.

| Local path below `native/semolina/` | Exact Semolina blob |
| --- | --- |
| `elf/ct_inverse_mod_256-armv8.S` | [`src/elf/ct_inverse_mod_256-armv8.S`][g-elf-inv-arm] |
| `elf/ct_inverse_mod_256-x86_64.s` | [`src/elf/ct_inverse_mod_256-x86_64.s`][g-elf-inv-x86] |
| `elf/pasta_add-armv8.S` | [`src/elf/pasta_add-armv8.S`][g-elf-add-arm] |
| `elf/pasta_add-x86_64.s` | [`src/elf/pasta_add-x86_64.s`][g-elf-add-x86] |
| `elf/pasta_mul-armv8.S` | [`src/elf/pasta_mul-armv8.S`][g-elf-mul-arm] |
| `elf/pasta_mulq-x86_64.s` | [`src/elf/pasta_mulq-x86_64.s`][g-elf-mulq-x86] |
| `elf/pasta_mulx-x86_64.s` | [`src/elf/pasta_mulx-x86_64.s`][g-elf-mulx-x86] |
| `coff/ct_inverse_mod_256-armv8.S` | [`src/coff/ct_inverse_mod_256-armv8.S`][g-coff-inv-arm] |
| `coff/ct_inverse_mod_256-x86_64.s` | [`src/coff/ct_inverse_mod_256-x86_64.s`][g-coff-inv-x86] |
| `coff/pasta_add-armv8.S` | [`src/coff/pasta_add-armv8.S`][g-coff-add-arm] |
| `coff/pasta_add-x86_64.s` | [`src/coff/pasta_add-x86_64.s`][g-coff-add-x86] |
| `coff/pasta_mul-armv8.S` | [`src/coff/pasta_mul-armv8.S`][g-coff-mul-arm] |
| `coff/pasta_mulq-x86_64.s` | [`src/coff/pasta_mulq-x86_64.s`][g-coff-mulq-x86] |
| `coff/pasta_mulx-x86_64.s` | [`src/coff/pasta_mulx-x86_64.s`][g-coff-mulx-x86] |
| `mach-o/ct_inverse_mod_256-armv8.S` | [`src/mach-o/ct_inverse_mod_256-armv8.S`][g-macho-inv-arm] |
| `mach-o/ct_inverse_mod_256-x86_64.s` | [`src/mach-o/ct_inverse_mod_256-x86_64.s`][g-macho-inv-x86] |
| `mach-o/pasta_add-armv8.S` | [`src/mach-o/pasta_add-armv8.S`][g-macho-add-arm] |
| `mach-o/pasta_add-x86_64.s` | [`src/mach-o/pasta_add-x86_64.s`][g-macho-add-x86] |
| `mach-o/pasta_mul-armv8.S` | [`src/mach-o/pasta_mul-armv8.S`][g-macho-mul-arm] |
| `mach-o/pasta_mulq-x86_64.s` | [`src/mach-o/pasta_mulq-x86_64.s`][g-macho-mulq-x86] |
| `mach-o/pasta_mulx-x86_64.s` | [`src/mach-o/pasta_mulx-x86_64.s`][g-macho-mulx-x86] |
| `win64/ct_inverse_mod_256-armv8.asm` | [`src/win64/ct_inverse_mod_256-armv8.asm`][g-win-inv-arm] |
| `win64/ct_inverse_mod_256-x86_64.asm` | [`src/win64/ct_inverse_mod_256-x86_64.asm`][g-win-inv-x86] |
| `win64/pasta_add-armv8.asm` | [`src/win64/pasta_add-armv8.asm`][g-win-add-arm] |
| `win64/pasta_add-x86_64.asm` | [`src/win64/pasta_add-x86_64.asm`][g-win-add-x86] |
| `win64/pasta_mul-armv8.asm` | [`src/win64/pasta_mul-armv8.asm`][g-win-mul-arm] |
| `win64/pasta_mulq-x86_64.asm` | [`src/win64/pasta_mulq-x86_64.asm`][g-win-mulq-x86] |
| `win64/pasta_mulx-x86_64.asm` | [`src/win64/pasta_mulx-x86_64.asm`][g-win-mulx-x86] |

[g-elf-inv-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/elf/ct_inverse_mod_256-armv8.S
[g-elf-inv-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/elf/ct_inverse_mod_256-x86_64.s
[g-elf-add-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/elf/pasta_add-armv8.S
[g-elf-add-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/elf/pasta_add-x86_64.s
[g-elf-mul-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/elf/pasta_mul-armv8.S
[g-elf-mulq-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/elf/pasta_mulq-x86_64.s
[g-elf-mulx-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/elf/pasta_mulx-x86_64.s
[g-coff-inv-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/coff/ct_inverse_mod_256-armv8.S
[g-coff-inv-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/coff/ct_inverse_mod_256-x86_64.s
[g-coff-add-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/coff/pasta_add-armv8.S
[g-coff-add-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/coff/pasta_add-x86_64.s
[g-coff-mul-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/coff/pasta_mul-armv8.S
[g-coff-mulq-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/coff/pasta_mulq-x86_64.s
[g-coff-mulx-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/coff/pasta_mulx-x86_64.s
[g-macho-inv-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/mach-o/ct_inverse_mod_256-armv8.S
[g-macho-inv-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/mach-o/ct_inverse_mod_256-x86_64.s
[g-macho-add-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/mach-o/pasta_add-armv8.S
[g-macho-add-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/mach-o/pasta_add-x86_64.s
[g-macho-mul-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/mach-o/pasta_mul-armv8.S
[g-macho-mulq-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/mach-o/pasta_mulq-x86_64.s
[g-macho-mulx-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/mach-o/pasta_mulx-x86_64.s
[g-win-inv-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/win64/ct_inverse_mod_256-armv8.asm
[g-win-inv-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/win64/ct_inverse_mod_256-x86_64.asm
[g-win-add-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/win64/pasta_add-armv8.asm
[g-win-add-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/win64/pasta_add-x86_64.asm
[g-win-mul-arm]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/win64/pasta_mul-armv8.asm
[g-win-mulq-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/win64/pasta_mulq-x86_64.asm
[g-win-mulx-x86]: https://github.com/supranational/semolina/blob/13ffc78074a6fbec44a4fd12b7f585a0bc1dc154/src/win64/pasta_mulx-x86_64.asm
