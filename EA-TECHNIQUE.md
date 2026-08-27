# Effective-affine / global-Z Eisenstein tables — rolling log

Branch: `effective-affine-globalz`, forked from `main` at
`72f219037b67de0247b358eff73803a2ad7bb23e`.
Decision platform: Apple M4 Max (16 cores), `aarch64-asm` field backend,
rustc 1.96.0. Regression guard: portable x86-64 (not yet run).

This file is the working log for the experiment. It records the
derivation, the staged measurements, and the final verdict
(SHIP / KERNEL ONLY / NO-GO). Re-read it fresh each session.

## Objective

Replace the eight-point Eisenstein `Table` builder's full normalization
(`window_proj` → `batch_normalize` over `8n` entries → `from_window`)
with an effective-affine construction in the style of `libsecp256k1`'s
odd-multiples table (pinned snapshot
`bitcoin-core/secp256k1@1c8babcd6c76dbea50bf4d65468dd8088d1b27a6`,
`secp256k1_ecmult_odd_multiples_table` / `secp256k1_ge_table_set_globalz`):

1. one projective double `D = 2P`, whose Jacobian `Z(D) = C` defines the
   isomorphic curve `y² = x³ + 5C⁶` on which `(X_D, Y_D)` is affine;
2. seven incomplete mixed additions by that effective-affine `D`, each
   returning its Z-ratio (`Z₃ = Z₁·2H`);
3. Eisenstein unit rotations folding the eight path points onto the
   eight canonical orbit representatives;
4. one backward cumulative-ratio pass bringing all eight entries to one
   omitted denominator `G`; the table's denominator on the original
   curve is `Z_T = C·G`.

The existing synchronized batch-affine ladder runs on those raw
coordinates unchanged (the a = 0 affine formulas never read b, and
independent lanes may sit on different effective curves — only the
per-table denominator must be common). Results return to the original
curve as `(x, y, Z_T)` with no inversion.

Scope guard: this is NOT a replacement for `Curve::batch_normalize`,
not a change to the public affine representation, and not a general
move onto isomorphic curves. Narrow, conversion-inclusive comparisons
only.

## Phase plan

- **Commit 1** — Sage derivation (`sage/effective_affine_chain.sage`) +
  Rust constants test. No behavior change. [DONE d1bacf4 — Sage run
  (passagemath via uv) prints the Rust constants verbatim and all
  assertions pass; the `effective_chain_derivation` test re-derives the
  chain exhaustively in Rust.]
- **Commit 2** — raw effective arithmetic: `RawJacobian`,
  `EffectiveAffine`, incomplete mixed add with ratio, unit application,
  backward global-Z pass, sealed `projective_unchecked`. Differential
  tests. No routing. [DONE 4f36193 — tests pass in release and debug
  (debug exercises the on-curve and ratio-consistency asserts).]
- **Commit 3** — `EffectiveTable` builder (+ batch) with entry tests and
  forced build benchmarks. [IN PROGRESS — builder + generic
  `batch_affine_ladder_raw` kernel (shared by `Table` and
  `EffectiveTable` through the private `WindowCoords` trait) +
  `bench_internals` hooks landed; all 237 tests pass under
  --all-features; the refactored kernel measured −1..−3% (parity or
  better) vs baseline on `batch hook/256|4096`, both curves. Forced
  build/build+mul/reuse benches running.]
- **Commit 4** — same-scalar sidecar: `try_batch_mul_same_scalar_effective`
  gated exactly by the existing batch-affine conditions; forced-backend
  benches.
- **Commit 5** — measured routing decision (threshold refit; do not
  inherit the 32-point gate).
- **Commit 6** — FFT paths: effective tables + one final n-point
  normalization instead of 8n table-entry normalization; gates are
  `curve-fft/affine-eisenstein-k11` (no regression) and `params/new-k11`
  (improve beyond noise).
- **Phase D (secondary, separate)** — prepared zero-check odd-multiple
  chains, projective α helper.

## The chain (verified)

Unit code order `[+1, -1, +ω, -ω, +ω², -ω²]` (as `JOINT_DIGITS`).

```
EFFECTIVE_CHAIN_UNITS = [2, 0, 5, 2, 4, 0, 0]   // +ω, +1, -ω², +ω, +ω², +1, +1
path: q0=1=Δ0, q1=3ω=ωΔ4, q2=2+3ω=ωΔ3, q3=1+4ω=ωΔ5,
      q4=-4-ω=ω²Δ6, q5=1+2ω=ωΔ1, q6=3+2ω=-ω²Δ2, q7=5+2ω=-ω²Δ7
EFFECTIVE_CHAIN_RELATIONS = [(0,0,f),(4,1,f),(3,1,f),(5,1,f),(6,2,f),(1,1,f),(2,2,t),(7,2,t)]
```

Exhaustive search over 6⁷ unit sequences: 54 valid chains (all stored
points in distinct target orbits, no pre-add state ±2), minimum 4
nontrivial rotations, 4 chains attain it; the pinned chain is the
lexicographically least. Pre-add states are never ±2 and never 0; all
`N(q_i ∓ 2)`, `N(q_i)` are small nonzero integers, so the additions are
nonexceptional and accumulators nonidentity at the group level for both
curves.

Scatter rule: for `q = ε·ω^r·Δ_slot`, `xs[e][slot] = ζ^((e−r) mod 3)·x_q`
and `ys[slot] = ε·y_q` (negative relation ⇒ `y_slot = −y_q`).

## Key repo facts (at fork point)

- `Table { xs: [[Base;8];3], ys: [Base;8] }`, `xs[e][i] = ζ^e·x([Δ_i]P)`;
  1 KiB. Builder: `window_proj` (7 full adds + endos) → shared
  `batch_normalize` → `from_window` (1 ZETA mul/entry).
- Ladder gate: `BATCH_AFFINE_MIN_POINTS = 32` live tables +
  `Decomposed::affine_ladder_safe`. Ladder: SoA affine accumulators,
  `batch_invert_nonzero` (two-lane, no zero handling) per column phase,
  fused ELM 2P+D on active columns; finalizes via `affine_unchecked`.
- `batch_normalize` is two-lane from 32 elements (`TWO_LANE_MIN = 32`),
  fused back-substitution — a strong baseline.
- FFT paths `mul_decomposed_same_scalar_affine` / `pairs_affine` build
  normalized tables, run ladders, return affine directly (no output
  normalization today). The effective variant must add one n-point
  normalization at the end — the win is 8n → n normalized entries.
- `CurveExtUnchecked::new_jacobian_unchecked` (crate-private, has
  `debug_assert!(is_on_curve)`) is the restoration constructor; expose
  through the GLV `private::Sealed` as `projective_unchecked`.
- Mixed add in `curves.rs` computes `Z₃ = (Z₁+H)² − Z₁² − H²`; the new
  helper uses `Z₃ = Z₁·2H` (saves the square, exposes the ratio).

## Measurements

### Baseline (clean `main` @ 72f2190, M4 Max, asm backend)

Raw log: scratchpad `baseline-main-72f2190.txt` (Criterion medians).

| row | Pallas | Vesta |
|---|---|---|
| `GLV table micro/build batch of 256` | 615.65 µs (2.405 µs/table) | 630.51 µs (2.463 µs/table) |
| `GLV table micro/use prebuilt table with 16 scalars` | 320.04 µs | 322.73 µs |
| `same-scalar batch/batch hook/32` (8-scalar corpus/iter) | 5.852 ms | 5.858 ms |
| `same-scalar batch/batch hook/256` | 39.96 ms | 40.08 ms |
| `same-scalar batch/batch hook/1024` | 156.5 ms | 156.6 ms |
| `same-scalar batch/batch hook/4096` | 622.9 ms | 617.7 ms |
| `curve-fft/native-k11` | 182.9 ms | — |
| `curve-fft/affine-eisenstein-k11` | 20.06 ms | — |
| `params/new-k11` | 25.57 ms | — |

(Each `same-scalar batch` iteration runs the whole 8-scalar corpus, so
per-point per-scalar cost at 4096 is ≈ 19.0 µs; the native loop at the
same size is ≈ 72 µs.)

### Commit 3 — forced same-build comparison (M4 Max, asm, serial)

Raw log: scratchpad `commit3-forced-tables.txt`. Medians, Pallas
(Vesta within ~1%):

| size | build norm | build eff | Δ build | build+mul norm | build+mul eff | Δ |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3.269 µs | 2.197 µs | −32.8% | — | — | — |
| 32 | 80.61 µs | 69.62 µs | −13.6% | 735.6 µs | 721.3 µs | −1.9% |
| 256 | 643.3 µs | 559.5 µs | −13.0% | 5.002 ms | 4.909 ms | −1.9% |
| 1024 | — | — | — | 19.61 ms | 19.30 ms | −1.6% |
| 4096 | 10.289 ms | 9.002 ms | −12.5% | 78.46 ms | 77.15 ms | −1.7% |

Reuse (prebuilt 256 tables × 16 scalars, ladder only): parity
(Pallas +0.1%, Vesta +0.5% — the effective representation does not slow
the ladder; reuse gate holds).

Reading: the effective builder is a reproducible ~13% cheaper than the
shared-normalization builder at scale (and 33% solo), but a table build
is only ~13% of build-plus-one-use, so the end-to-end same-scalar win
is ~1.6–2.0%. Consistent across both curves and all sizes; noise on
these rows is ~±0.3%. The refactored generic ladder kernel itself
measured −1..−3% vs baseline on the production `batch hook` rows
(parity or slightly better), so none of the above is kernel drift.

### Commit 4/5 — routed grid and gate refit (M4 Max, asm, serial)

Raw logs: scratchpad `commit4-same-scalar-grid.txt`,
`commit5-gate-refit.txt`.

Routed `batch hook` (effective sidecar at ≥ 32 live) vs same-build
`forced normalized`, medians over the 8-scalar corpus per iteration:

| size | Pallas routed | Pallas norm | Δ | Vesta routed | Vesta norm | Δ |
|---:|---:|---:|---:|---:|---:|---:|
| 32 | 5.745 ms | 5.854 ms | −1.9% | 5.872 ms | 6.016 ms | −2.4% |
| 256 | 39.21 ms | 39.83 ms | −1.6% | 40.03 ms | 41.06 ms | −2.5% |
| 1024 | 154.6 ms | 156.2 ms | −1.0% | 157.0 ms | 161.9 ms | −3.1% |
| 4096 | 618.9 ms | 626.9 ms | −1.3% | 630.1 ms | 647.9 ms | −2.7% |

Effective wins at every gated size on both curves; sub-gate rows are
identical code and differ by noise only. Row-to-row noise on long rows
is ~1–2%, so the per-row magnitudes are soft but the sign is uniform
across 16 gated cells.

Gate refit (forced build+mul across the gate; normalized = production
fallback with per-point Jacobian ladders below 32, effective = batched
kernel forced at every size): at 4 points effective is +110%, at 8
+46%, at 16 +13%, at 32 −1.4%, at 64 −1.9% (both curves agree). The
build-cost saving does not move the ladder-vs-Jacobian crossover out of
the (16, 32] interval, so the sidecar keeps the existing
`BATCH_AFFINE_MIN_POINTS = 32` gate — no separate threshold constant.

## Verdict

[pending]
