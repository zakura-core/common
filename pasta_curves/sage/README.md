# SageMath derivations of the crate's constants

The scripts in this directory recompute, from the curve definitions
alone, the magic constants that appear in the crate's source, printing
them in the exact shape of the Rust code so the two can be diffed:

- `glv_constants.sage` — the GLV short-basis and Babai-rounding
  constants in the `GlvParams` implementations in `src/glv.rs`
  (`V1A`, `V1B_NEG`, `V2A`, `V2B`, `G1`, `G2`, for both curves).
- `glv_boundary_scalars.sage` — the `*_BOUNDARY_SCALAR` witnesses used
  by the `babai_boundary_*` and `native_vs_glv_boundary_*` regression
  tests in `src/glv.rs`.
- `cm_constants.sage` — the quadratic CM/AMNS representation constants
  in the `CmParams` implementations in `src/fields/cm.rs` (the reduced
  generator `T`/`M`/`M0`, `I0`/`I1`, `ONE`, `SIGMA`, `BETA_INV`,
  `SIGMA_BETA_INV`, `SOLINAS_C`, and the 512-fractional-bit Babai
  constants `G_T`/`G_M`), plus the rounding-tie scalar test vectors.
  The same values are re-verified in-crate by compile-time assertions
  and the `cm_field_tests!` suites.

The scripts use exact integer/rational arithmetic and hand-rolled
lattice reduction only, so their output is deterministic and does not
depend on the SageMath version.

## Running

Sage is pinned via [uv](https://docs.astral.sh/uv/) using
[passagemath](https://pypi.org/project/passagemath-standard/), the
pip-installable distribution of SageMath (see `pyproject.toml` /
`uv.lock`). From this directory:

```console
$ uv run sage glv_constants.sage
$ uv run sage glv_boundary_scalars.sage
```

Any reasonably recent standalone SageMath installation works too:
`sage glv_constants.sage`.
