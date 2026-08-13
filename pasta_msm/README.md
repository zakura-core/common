# Zakura Pasta MSM

`zakura-pasta-msm` provides caller-thread, variable-time multiscalar
multiplication for the Pallas and Vesta curves. It is a CPU-only, attributed
Zakura fork of Supranational's `pasta-msm`, Semolina, and Sppark projects.

The public API consists of `pallas_vartime` and `vesta_vartime`. Both require
equal-length slices and return the identity for empty inputs. They provide no
constant-time guarantee and should be used only where variable-time behavior
is acceptable, such as Halo proof generation.

The Zakura-specific package name avoids colliding with Supranational's
`pasta-msm` release lineage. The Rust library name remains `pasta_msm`.

The native backend contains no CUDA or GPU path, verifiable-delay-function
(VDF) workload, process-global thread pool, or internal worker threads. Each
call executes on its Rust caller's thread. For a non-identity result, one field
inversion is required to normalize the final MSM result. See
[`UPSTREAM.md`](UPSTREAM.md) and
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) for provenance.

The initial backend supports `aarch64` and `x86_64` targets. Other target
architectures are rejected by the build script.

## Assembly

Consumers compile checked-in Semolina assembly for their Cargo target and do
not need Perl. Maintainers can verify every generated output with:

```console
./native/asm/regenerate.sh --check
```

## License

Licensed under Apache License 2.0. See [`LICENSE-APACHE`](LICENSE-APACHE).
