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

Machine: **Apple M4 Max** (12P+4E, macOS 26.5.2, arm64) · rustc 1.96.0 · Criterion 0.4, default
sampling · captured at `a76eb1a` (bench-extension commit, Montgomery arithmetic unchanged).
Baselines: `mont-portable` (default features per bench target), `mont-asm` (`+aarch64-asm`);
saved as Criterion baselines of those names, and pinned here because `target/criterion` is
ephemeral. Chain benches report the whole 64-op chain; per-op = value/64.

### Field operations (Fp / Fq medians)

| benchmark | Fp mont-portable | Fp mont-asm | Fq mont-portable | Fq mont-asm |
|---|---|---|---|---|
| mul_assign | 11.11 ns | 8.64 ns | 11.12 ns | 8.75 ns |
| square | 9.62 ns | 9.62 ns | 9.61 ns | 9.57 ns |
| mul_chain/64 (latency) | 1.001 µs (15.6/op) | 742.5 ns (11.6/op) | 992.9 ns | 739.8 ns |
| square_chain/64 | 935.0 ns (14.6/op) | 930.7 ns | 927.8 ns | 932.6 ns |
| mul_indep/4 (ILP) | 36.50 ns (9.1/op) | 30.84 ns (7.7/op) | 36.50 ns | 30.53 ns |
| mul_indep/8 | 72.38 ns (9.0/op) | 61.22 ns (7.7/op) | 72.23 ns | 61.05 ns |
| add_assign / sub_assign / neg / double | 2.65–2.76 ns | 2.64–2.76 ns | ~same | ~same |
| add_chain/64 | 256.3 ns (4.0/op) | 256.9 ns | 256.2 ns | 255.8 ns |
| invert (divstep) | 759.4 ns | 754.4 ns | 756.1 ns | 759.6 ns |
| sqrt | 4.358 µs | 3.013 µs | 4.377 µs | 3.003 µs |
| pow_vartime_(p\|q)−2 | 4.882 µs | 3.895 µs | 4.832 µs | 3.826 µs |
| to_repr | 10.30 ns | 10.12 ns | 10.30 ns | 10.08 ns |
| from_repr | 12.23 ns | 9.83 ns | 12.19 ns | 9.81 ns |

Deferred inner products (Fp; Fq within noise of the same values):

| length | lazy portable | lazy asm | eager portable | eager asm |
|---|---|---|---|---|
| 100 | 546.9 ns | 550.1 ns | 1.295 µs | 954.3 ns |
| 1024 | 5.560 µs | 5.563 µs | 13.271 µs | 9.750 µs |
| 10000 | 54.17 µs (5.4 ns/term) | 54.30 µs | 129.8 µs | 95.2 µs |

### Curve-level (Pallas; Vesta within noise)

| benchmark | mont-portable | mont-asm |
|---|---|---|
| point doubling | 114.9 ns | 84.4 ns |
| point addition | 228.6 ns | 173.0 ns |
| point to_affine | 239.7 ns | 228.7 ns |
| batch_normalize/1000 | 92.7 µs | 70.0 µs |
| native scalar mul | 89.1 µs | 67.7 µs |
| mul_glv one-shot | 27.5 µs | 21.1 µs |
| GLV table mul (reused) | 25.0 µs | 18.9 µs |
| same-scalar batch hook /128 | 27.3 ms | 20.5 ms |
| hash-to-curve | 12.80 µs | 9.05 µs |

Early observations against the predictions:
- The asm **square is no faster than portable square** (9.6 ns both) while asm mul is (8.6 vs
  11.1 ns) — squaring is already reduction-dominated, consistent with the spec's warning that
  square chains are the CM risk case.
- Dependent-mul latency (15.6 ns/op portable) far exceeds throughput (9.0 ns/op with 8-way ILP):
  there is real serial-dependency headroom for CM's independent product chains to attack.
- add/sub at 2.7 ns are already cheap; the CM lattice normalizer has to stay within ~a ns of this.

### CM measurement columns (filled at M5)

| benchmark | mont-portable | mont-asm | cm-portable | predicted | measured Δ | explanation |
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
