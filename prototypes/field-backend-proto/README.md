# field-backend-proto

Prototype backends for Pallas base-field (`Fp`) arithmetic on Apple AArch64,
exploring how to eliminate the FFI-boundary cost of the `aarch64-asm` backend
in `pasta_curves`. Standalone crate (not a workspace member); everything is
benchmarked head-to-head in one binary so measurements are adjacent and share
machine state.

## Variants

| feature | contents |
|---|---|
| (always) | **baseline**: renamed copy of the vendored Semolina assembly, called via `extern "C"` — identical machine code to the real backend |
| `v1` | sparse-modulus portable Rust (CIOS specialized to `p[2]=0`, `p[3]=2^62`), fully inlinable |
| `v2` | Semolina's arithmetic as inline `asm!` blocks, register operands, `options(pure, nomem, nostack)` |
| `v3` | hand-fused Jacobian `point_double_n` in assembly (dbl-2009-l, a=0), field ops macro-inlined over a fixed stack frame |

Correctness: `cargo test` differentially checks every enabled variant against
`pasta_curves` (`Fp` arithmetic and `pallas::Point` doubling), limb-exact.

## Results (Apple M-series, 2026-08-17)

Serial dependency chains; ns per operation.

| | mul | sqr | Jacobian double |
|---|---|---|---|
| now: portable inline (`Fp::mul`/`Fp::square`) | 23.9 | 22.3 | — |
| now: FFI asm (vendored backend) | 22.5 | 23.3 | 180 (composed) |
| now: `pallas::Point::double` | — | — | 166 |
| v1: sparse portable | 21.3 | 21.5 | 204 (composed) |
| v2: inline asm | **17.4** | **17.3** | **130 (composed)** |
| v3: fused asm | — | — | 148 (n=1/call), 144 (one call) |

## Conclusions

1. **v2 (inline `asm!`) wins everywhere**: ~22-26% faster field ops than
   either current path, and 22% faster doubling than `pallas::Point::double`.
2. **v2-composed beats the hand-fused v3** (130 vs 144 ns/double): LLVM
   register-allocating between pure `asm!` blocks outperforms a hand-fused
   routine that round-trips a stack frame — hand fusion at the group-op
   level is unnecessary once the primitives are inline asm.
3. **v3 still beats the status quo** (−13% vs `Point::double`) with per-call
   overhead nearly amortized even at n=1 (148 vs 144), but it is dominated
   by v2 and carries the largest audit burden (novel hand-written assembly).
4. **v1 is a modest standalone win** (−5–11%) and works on every AArch64
   target with no `unsafe`, but composes poorly: fully inlining seven CIOS
   bodies per doubling causes register-pressure spills (204 ns/double).

Implication for `[ivk]epk` (GLV ladder ≈ 127 doubles + ~51 mixed adds):
v2-style primitives project to roughly **20% faster scalar multiplication**,
on top of PR #65's exponentiation-chain gains.

## Running

```sh
cargo test                 # differential correctness vs pasta_curves
cargo bench                # all enabled variants, one binary
```

Per-prototype branches select variants via default features; on the
integration branch all three are enabled.
