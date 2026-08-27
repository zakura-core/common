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
  Rust constants test. No behavior change. [DONE — script written,
  Sage run pending uv install; math verified by independent Python
  harness: 54 valid chains, 4 minimal at 4 rotations, pinned chain is
  the lexicographically least minimal one.]
- **Commit 2** — raw effective arithmetic: `RawJacobian`,
  `EffectiveAffine`, incomplete mixed add with ratio, unit application,
  backward global-Z pass, sealed `projective_unchecked`. Differential
  tests. No routing.
- **Commit 3** — `EffectiveTable` builder (+ batch) with entry tests and
  forced build benchmarks.
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

## Verdict

[pending]
