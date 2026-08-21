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
- **M1 (kernel, `src/fields/cm.rs`)**: params trait + wide primitives + Karatsuba ring
  products + the corrected adapted-basis lift + branchless lattice normalizer, all
  differential-tested against the live Montgomery fields (10k random per op + corners).
  Two real width bugs found and fixed beyond the spec's warnings: **the sum `V + q·g`
  spans 257 bits** (|V0 + (q·g)0| ≤ ~1.55·2^255 — a 256-bit two's-complement register pair
  silently wraps while the low-half exactness check still passes), fixed with a fused
  add-shift carrying signed-extension bits; and **the σ-component of `q·g` alone spans 258
  bits** (≤ 2^127·(4m+|t|) ≈ 2.31·2^254), fixed with a 320-bit lane (`W320`). Also: a zero
  Karatsuba middle term must not charge its sign's borrow. The stepwise diagnostic
  `reduce_intermediates_match_oracle` oracle-checks every reducer intermediate — built for
  (and battle-tested by) exactly these bugs; the future asm backend should be debugged
  against it.
- **M2 (conversions)**: 512-fractional-bit Babai encode (384 GLV-style bits provably admit
  ±1 slips the CM margins cannot absorb), Solinas decode, const `from_raw` ladder.
  Rounding-tie scalars are computed in-test from field inverses of t and m.
- **M3 (`cm-field` feature swap)**: intra-file cfg pairs in fp.rs/fq.rs; `MODULUS` retyped
  to `MODULUS_LIMBS` and the GPU contract pinned to Montgomery constants by hex-literal
  tests; `ct_eq` = normalized-sub + raw-zero test; serialization byte-identity pinned by
  `repr_pinned_vectors` in both modes. Const-eval cost of 67 `from_raw` ladders: none —
  the cm-field crate rebuild is *faster* than the Montgomery one (3.7s vs 11.8s; the
  Montgomery const path is itself const-heavy).
- **M4 (inversion + deferred)**: divstep seed parameterized (`InvParams::SEED`; Montgomery
  sets keep R², canonical sets seed 1 — batch counts proven seed-independent against the
  reference driver and the pinned adversarial vectors); CM `invert` =
  decode→divstep→encode. Deferred Phase B: `CmProduct` accumulates 320-bit sums of raw
  ring products (2^63-product headroom); finalize = one extra pass-1 fold (÷2^128) + the
  standard reduction (÷β) + ×`TWO_POW_259` (≡ 2^128·β mod g, itself a ÷β) for a net ÷β —
  the scale bookkeeping here is easy to get wrong (a naive fold+reduce divides by 2^259,
  not β).

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

### M5 measurement: cm-portable vs both baselines

Same machine/toolchain as the baselines; Fp shown, Fq within noise (full data in the
`cm-portable` Criterion baseline). Ratios are cm-portable ÷ baseline.

| benchmark | mont-portable | mont-asm | cm-portable | ×portable | ×asm | prediction → what actually happened |
|---|---|---|---|---|---|---|
| mul_assign | 11.11 ns | 8.64 ns | 34.47 ns | 3.10 | 3.99 | predicted ~parity (27 vs 28 mul-class). WRONG for portable code: the count applies to hand-scheduled asm. Portable CM pays sign/magnitude extraction + conditional negation around every product, wide-carry bookkeeping (the 257/258-bit lanes), the centering/lift arithmetic, and — biggest single miss — `s·g` as four full 128×128 products (~24 extra mul-class) where the asm plan uses shifts/adds on the tiny s0, s1. |
| square | 9.62 ns | 9.62 ns | 28.40 ns | 2.95 | 2.95 | the dedicated formula does help (18% below CM mul), but reduction dominates exactly as the spec warned. |
| mul_chain/64 (per op) | 15.6 ns | 11.6 ns | 38.4 ns | 2.45 | 3.31 | CM's chain ratio is *better* than its throughput ratio — the independent product chains do overlap — but from a 3× deficit that only softens the loss. |
| mul_indep/8 (per op) | 9.0 ns | 7.7 ns | 33.9 ns | 3.74 | 4.43 | Montgomery gains more from ILP than CM does portably: CM's dependent carry/mask scalar ops saturate the ALUs before the multiplier is the bottleneck. |
| add_assign / sub_assign | 2.7 ns | 2.7 ns | 4.1/4.3 ns | ~1.55 | ~1.55 | the two-phase masked lattice normalizer costs ~1.4 ns over the single conditional modulus subtract. |
| add_chain/64 (per op) | 4.0 ns | 4.0 ns | 4.8 ns | 1.19 | 1.19 | chained, the normalizer pipelines well — the closest CM gets to Montgomery on any hot op. |
| neg | 2.66 ns | 2.69 ns | 2.58 ns | 0.97 | 0.96 | the one outright win: coefficient negation beats subtract-from-modulus. |
| invert | 759 ns | 754 ns | 827 ns | 1.09 | 1.10 | divstep core unchanged; the decode+encode sandwich adds ~70 ns — consistent with to_repr+from_repr below (26+37 ns). Slightly above the "low single digits" prediction because conversions are pricier than predicted. |
| to_repr | 10.3 ns | 10.1 ns | 26.1 ns | 2.53 | 2.58 | predicted slower (linear form + Solinas); measured 2.5×. |
| from_repr | 12.2 ns | 9.8 ns | 37.3 ns | 3.05 | 3.79 | predicted slower (canonicalize + 512-bit Babai); measured 3×. |
| sqrt | 4.36 µs | 3.01 µs | 10.25 µs | 2.35 | 3.40 | tracks the square-chain ratio (the addition chain is ~250 squarings); the 4 decode-priced hash lookups are noise at this size. |
| pow_vartime(p−2) | 4.88 µs | 3.90 µs | 10.73 µs | 2.20 | 2.75 | fused-chain workload, tracks square/mul ratios. |

Curve level (Pallas; Vesta within noise) and deferred:

| benchmark | mont-portable | mont-asm | cm-portable | ×portable | ×asm |
|---|---|---|---|---|---|
| point doubling | 114.9 ns | 84.4 ns | 300.0 ns | 2.61 | 3.55 |
| point addition | 228.6 ns | 173.0 ns | 621.5 ns | 2.72 | 3.59 |
| batch_normalize/1000 | 92.7 µs | 70.0 µs | 257.0 µs | 2.77 | 3.67 |
| native scalar mul | 89.1 µs | 67.7 µs | 235.1 µs | 2.64 | 3.47 |
| mul_glv one-shot | 27.5 µs | 21.1 µs | 67.2 µs | 2.44 | 3.18 |
| GLV table mul (reused) | 25.0 µs | 18.9 µs | 61.9 µs | 2.48 | 3.28 |
| hash-to-curve | 12.8 µs | 9.1 µs | 28.7 µs | 2.24 | 3.17 |
| inner_product_lazy/10000 (per term) | 5.4 ns | 5.4 ns | 11.8 ns | 2.18 | 2.18 | 
| inner_product_eager/10000 (per term) | 13.0 ns | 9.5 ns | 37.3 ns | 2.87 | 3.91 |

Curve ratios are a direct blend of the mul/square ratios (point arithmetic is
product-dominated). The deferred *lazy* ratio (2.18×) beats the raw mul ratio (3.10×): the wide
accumulator amortizes the whole reduction — the Phase B design works as intended, it just sits
on top of a slower product.

### M5 verification

Downstream, under `--features zakura-pasta-curves/cm-field` feature unification on the Apple
host (which also co-enables `aarch64-asm` via halo2's target dependency — the silent-disable
path exercised end-to-end): `zakura-orchard`, `zakura-halo2-proofs` (incl. the 275 s plonk
suite), `zakura-halo2-gadgets` + `zakura-halo2-poseidon`, `zakura-reddsa` + `zakura-sinsemilla`
— 31 test binaries, zero failures. One real downstream finding along the way: halo2_poseidon's
192-element `ROUND_CONSTANTS` tripped rustc's `long_running_const_eval` on the original
256-step const `from_raw` ladder, which forced `from_raw` to become a const-evaluable Babai
conversion (better in every way; the ladder survives as a test-only reference).

## Verdict after the portable pass (M5)

- Portable CM loses 2.2–3.8× across every workload that matters; only `neg` wins and `invert`
  nearly ties. The spec's operation-count near-parity is an asm-only statement: portable code
  cannot express "3 independent mul/umulh chains + carry flags + shift-add small scalars", and
  LLVM's schedule of the Montgomery mac/adc idiom is extremely good.
- The M6 question is therefore: can hand-scheduled asm close a **4.0× gap** to mont-asm mul
  (34.5 → 8.6 ns)? The instruction budget (≈48 vs ≈52 mul-class) says the *multiplier* work is
  comparable, so the answer hinges entirely on whether the lift/normalize carry traffic and
  register pressure stay near-free. The latency-vs-throughput data (mont-asm mul: 11.6 ns/op
  dependent vs 7.7 ns/op at 8-way ILP) shows real headroom for CM's independent chains in
  latency-bound point arithmetic — the only plausible path to a win, and it must overcome the
  measured 3.3× chained deficit.
- Everything non-mul that CM makes structurally slower (conversions 2.5–3.8×, sqrt via square
  chains, deferred eager) stays slower even with perfect mul asm.

**Recommendation: do not replace Montgomery on this evidence.** A bounded M6 spike (the fused
mul kernel only, measured against `mont-asm` before writing square/sqr_n_mul) is the cheapest
way to settle the spec's actual question definitively; anything beyond that spike is only
justified if the spike lands within ~10% of mont-asm mul.

## Decision log (continued)

- 2026-08-20 (M5): portable pass complete; `cm-field` is correct, byte-compatible, and fully
  green crate-wide and downstream, but 2.2–3.8× slower portably. Paused for a go/no-go on the
  M6 asm spike per the plan.

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

## Next pass: M6 AArch64 backend / M7 decision (resumable roadmap)

This section is the hand-off for the next session: everything needed to build and judge the
hand-scheduled backend without this pass's session context.

### M6 — hand-scheduled Apple AArch64 backend

**Files/gating.** New `src/fields/cm_aarch64.rs`, module gate
`#[cfg(all(feature = "aarch64-asm", feature = "cm-field", target_arch = "aarch64",
target_vendor = "apple"))]`, `#[allow(unsafe_code)]`, registered in `src/fields.rs` beside
`aarch64_asm` (whose gate carries `not(cm-field)` since M3). A looped routine goes in
`src/asm/pasta_mul-armv8.S` under a new symbol (e.g. `_pasta_curves_cm_sqr_n_mul`); the file is
already compiled whenever `aarch64-asm` is on, `build.rs` unchanged. When this lands, remove the
"silently disabled" caveat from the Cargo.toml feature comment and make
`mul_runtime`/`square_runtime`/`sqr_n_mul_runtime` in fp.rs/fq.rs three-way:
`(asm ∧ ¬cm)` → `aarch64_asm`, `(asm ∧ cm)` → `cm_aarch64`, else portable. `to_repr` keeps its
portable CM arm.

**Kernels, in order.** (1) fused ring-mul + full two-pass reduction (inline `asm!`,
register-only, `options(pure, nomem, nostack)`, matching `aarch64_asm.rs` style; constants
T/M/M0/I0/I1 via `mov/movk` or passed in); (2) dedicated square (`V0 = a²−3b²`,
`V1 = 2ab+3b²` + the same reduction); (3) looped `sqr_n_mul` keeping the packed (a,b)
accumulator in registers (branching loop ⇒ the stable-frame `.S` form, same reason as the
Montgomery one); intermediate iterations may stay in the wider closure box without
re-normalization. Only if profiling shows them hot: add/sub or encode/decode asm (expected
unnecessary — LLVM schedules the short i128 sequences well; portable add is already 2.7 ns).

**Instruction budget (target: Montgomery asm ≈ 52 mul-class; measured mont-asm mul = 8.6 ns).**
Ring product: 3 coefficient products × subtractive Karatsuba = 9 `mul` + 9 `umulh`. Pass-1
`q = −V·I mod M`: 3 low-only 128×128 products ≈ 12 mul-class (only 3 `umulh` — keep low-only
muls from emitting `umulh`). `q·g`: 3 full 128×128 = 18. Total ≈ 48 mul-class + adds/shifts for
the 3-bit lift and `s·g` (s0 ∈ [−16,16], s1 ∈ [−4,4] — shift/add, no general muls).
**Carry-width traps the asm must reproduce (see the M1 log entry):** `V + q·g` needs a 257th
bit (fused add-shift with signed-carry extension) and the σ-component of `q·g` needs a 320-bit
lane — both are one extra `adc`-class op each, but forgetting them is silent corruption that
only the stepwise test catches.

**Scheduling strategy (the whole point).** The three chains `u = a·c`, `v = b·d`,
`w = (a+b)(c+d)` are independent — interleave their `mul`/`umulh` streams to hide the ~3-cycle
multiplier latency (measured headroom: dependent-chain mul 15.6 ns/op portable vs 9.0 ns/op at
8-way ILP). Pass-1's three low products depend only on `V.lo` — start them as the w-chain tail
retires; `q·g`'s three chains interleave again. Register budget is the top risk: 8 operand
words + ~18 in-flight product halves + constants against ~28 usable GPRs. Plan: small constants
as immediates, reuse the (a+b)/(c+d) transients, prefer recomputing one low product over
spilling.

**Contract + tests.** Document the register-level contract (inputs satisfy the storage
invariant `|a| < 31·2^122, |b| < 3·2^124`; outputs re-establish it — the analog of the
Montgomery canonicity contract at the top of `aarch64_asm.rs`). Clone the differential harness
as `cm_aarch64_matches_portable_arithmetic`: boundary elements (zero, one, −one, max-box
coefficients via `cm::pack`, `from_raw([u64::MAX; 4])`), 1024 random pairs, `sqr_n_mul`
n ∈ {1, 2, 7, 129}, `to_repr`/`ct_eq` cross-checks against the portable kernel. Debug against
`reduce_intermediates_match_oracle` (it pinpoints the first broken reducer step). CI: add a
macOS smoke step under `--all-features` filtering the new test (the Montgomery smoke step
stays pinned to explicit features).

**Exit criteria.** (i) differential green on Apple hardware; (ii) **no stack traffic** in the
disassembly of the mul/square kernels (`objdump -d`/`cargo asm` — a spilling kernel forfeits
the win); (iii) `cm-asm` Criterion baselines captured for fp/fq/point/glv/deferred and recorded
here against `mont-asm`.

### M7 — replace-or-demote decision

**Inputs (recorded here):** field microbenches portable+asm both fields; curve-level `point` +
`glv` (incl. same-scalar batches); deferred lazy/eager; downstream
`cargo bench -p zakura-halo2-proofs --bench plonk` (+ `arithmetic`, `fft`) and orchard benches
under `--features zakura-pasta-curves/cm-field` unification, with matching Montgomery baselines;
x86-64 portable numbers if a machine is available.

**Decision rule.** Replace/demote Montgomery only if representative curve-level AND downstream
workloads win asm-vs-asm on Apple and do not regress on portable x86-64. Otherwise `cm-field`
stays an experimental opt-in with the full verification matrix kept green in both modes.

**Flip mechanics (its own PR, only on a win):** swap cfg polarity (CM default; Montgomery
behind an opt-out feature or removed after a deprecation window); re-pin the CI matrix (keep an
explicit Montgomery leg while it exists); CHANGELOG entry with measured numbers (divstep
precedent recorded I/M ≈ 77); GPU constants unaffected (they publish Montgomery values by
contract, pinned by `gpu_constants_are_montgomery`); Montgomery `.S` routines removed only when
Montgomery is removed; downstream manifests untouched (features are additive).

**Parked optimization items (record, don't do):** perfect-hash sqrt keyed on a cheap CM normal
form (needs a canonical representative — research task; params regenerated via zcash/pasta's
`squareroottab.sage`); asm encode/decode; deferred-accumulator asm; a dedicated `from_u64`
short-circuit (currently the full Babai path).
