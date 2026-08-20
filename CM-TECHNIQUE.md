# Quadratic CM/AMNS field representation for the Pasta curves

Rolling design/benchmark record for the `cm-field` experiment: replacing the Montgomery
representation of `pasta_curves::{Fp, Fq}` with coefficient pairs `(a, b)` meaning
`a + b·σ ≡ β·x (mod g)` in `Z[σ]/(σ² − 3σ + 3)`, where `g = t + m·σ`, `Norm(g) = r ∈ {p, q}`,
and `β = 2^131`. This document is updated at every milestone; benchmark numbers live here because
`target/criterion` data is ephemeral.

Companion docs: `TECHNIQUE.md` (the variable-time 62-divstep inversion this crate already uses),
`AUDIT.md` (the Apple AArch64 Montgomery assembly audit).

## Representation summary

- Storage: the existing 32-byte `Fp([u64; 4])`; limbs `[0..2]` = `a` (two's-complement i128),
  limbs `[2..4]` = `b`. Invariant `|a| < 31·2^122`, `|b| < 3·2^124`.
- Multiplication: Karatsuba ring product (`u = ac`, `v = bd`, `w = (a+b)(c+d)`;
  `V0 = u − 3v`, `V1 = w − u + 2v`) — 9 full 64×64 word products — followed by a two-pass
  reduction by `β = 8·2^128`: a Montgomery-style pass modulo `2^128` (via `g⁻¹ mod 2^128`), then
  the **adapted-basis 3-bit lift**: the full quotient is centered in the lattice basis
  `w1 = g, w2 = (σ−3)·g` (coordinates `X, Y ∈ [−β/2, β/2)`), not coefficientwise — the
  coefficientwise version does not satisfy the closure proof.
- Addition/subtraction: at most one `w2 = (−3m0, t)` correction then one `w1 = (t, m)` correction,
  branchless. Equality: representation is redundant; `ct_eq` = normalized subtract + raw zero
  check ((0,0) is the only lattice point in the normalizer's output box).
- Per-field roots: Fp uses σ = ζ + 2; Fq uses σ = ζ² + 2 (ζ = the crate's `ZETA`); in both cases
  the unique associate of the generator with `t ≡ 1, m ≡ 0 (mod 8)`.
- Feature: `cm-field` (experimental). Montgomery remains the default. Under
  `cm-field + aarch64-asm` the Montgomery assembly backend is silently disabled until a CM
  backend exists (M6).

## Milestone log

- **M0 (PR-1)**: bench extensions (`mul_chain/64`, `mul_indep/{4,8}`, `square_chain/64`,
  `add_chain/64`, `pow_vartime_{p,q}_minus_2`, `benches/deferred.rs` lazy-vs-eager inner
  products) + Montgomery baselines captured below, BEFORE any arithmetic change.
  Note: the plan named a `pow_by_t_minus1_over2` bench, but `SqrtTableHelpers` is
  `pub(crate)`-only (`src/arithmetic.rs:11`); `pow_vartime(p−2)` exercises the same fused
  `sqr_n_mul` machinery through public API and doubles as the Fermat-inversion cost reference.

## Benchmark record

Machine: (filled at capture) · Toolchain: (filled at capture) · Criterion 0.4, default sampling.
Baselines: `mont-portable` (default features per bench target), `mont-asm` (`+aarch64-asm`).

### Apple M-series (primary)

_To be filled by the baseline capture (PR-1) and per-milestone measurement runs._

| benchmark | mont-portable | mont-asm | cm-portable | predicted (cm vs mont-portable) | measured Δ | explanation |
|---|---|---|---|---|---|---|

## Predictions to test (from the operation-count analysis)

- `mul`: ~27 vs ~28 x86 mul-class; ~48 vs ~52 AArch64 mul/umulh-class; 1 big pass + 3-bit lift vs
  4 serial Montgomery rounds → expect parity-to-small-win portable; the asm-vs-asm comparison is
  the real bar.
- `add/sub/neg`: cheaper (no full 256-bit modulus subtraction; two masked i128 corrections).
- `square`: the risk case — raw product cheaper, reduction unchanged.
- `to_repr`/`from_repr`: slower (linear form + Solinas; Babai encode).
- `invert`: low-single-digit % slower (divstep core unchanged + decode/encode sandwich).
- `sqrt`: ~1–2% slower (4 perfect-hash lookups price a decode each).
- Deferred inner products: Phase A (eager) loses vs Montgomery lazy by design; Phase B restores.

## Decision log

- 2026-08-20: experiment started on branch `cm-field`; scope M1–M5 portable, then pause for a
  go/no-go on the hand-scheduled AArch64 backend (M6).

## Next pass: M6 AArch64 backend / M7 decision

_Placeholder — filled in at M5 with the resumable roadmap (files/gating, kernels, instruction
budget, scheduling strategy, dispatch, contract/tests, exit criteria; M7 decision rule and flip
mechanics), updated with everything learned in M1–M5._
