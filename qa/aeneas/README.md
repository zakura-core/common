# Aeneas proofs of Common's Udon arithmetic

This package ports the Udon arithmetic proofs to Common's production source
at revision `30eeb939123414887642f1cdb60ea59ab13bdf7c`. It extracts the actual
Rust module with Charon and Aeneas and checks the proof terms with Lean.
Production arithmetic is unchanged by this package.

The strict census checks 1,723 named declarations in 391 authored proof
modules. All five layers and every item in the arithmetic/API checklist are
proved for both Pasta fields, under their stated input contracts. This includes
Fp/Fq modular multiplication, inversion, square roots, canonical encodings,
byte reduction, portable and AArch64 Rust product sums, and array/iterator
wrappers. The latest completed incremental evidence is
[evidence/product-dot-iter.json](evidence/product-dot-iter.json).

The final fresh replay is incomplete. It recorded 1,380 successful module
compilations, including all 70 model files and 271 of 732 certificate-checking
modules. Two checking processes exited 137 without Lean diagnostics. The cause was not
established. The final complete replay and its strict census remain pending;
[evidence/full-replay-incomplete.json](evidence/full-replay-incomplete.json)
records the attempted commands, exit codes and source hashes.

The five layers, bottom up, are:

1. Words: exact word operations, carries, borrows and split products.
2. Multi-limb integers: comparisons, addition, subtraction, wide products and squares.
3. Montgomery arithmetic: reduction and the portable arithmetic kernels.
4. Fp/Fq operations: core arithmetic, representations and integer constructors.
5. Further APIs: codecs, byte reduction, roots, square roots, inversion and product sums.

These are this package's organization, rather than layers prescribed by
Aeneas. [CHECKLIST.md](CHECKLIST.md) records the milestones and validation
status. The descriptions below state the functional contracts and translation
boundary. Later milestone sections preserve their historical counts and
then-outstanding obligations.

The proofs assume valid loose (`< 2p`) or reduced (`< p`) representations.
Generic iterator contracts also require successful conversions and length
calls, finite error-free traces and the stated length/zip behavior. They do
not prove that arbitrary custom iterators terminate or report correct lengths.
Elliptic-curve point operations, scalar multiplication, MSM, GLV, point
encodings, constant-time behavior and the optional `aarch64-asm` implementation
are outside this checklist.

Coverage is limited to the named declarations in [catalog.json](catalog.json),
not every API in Common's field module. Additional field paths outside these
proofs include batch inversion and its scaled/grouped variants; FFT/butterfly
kernels and their power-of-two scaling; fraction-prefix, power-fill and
constant-prefix helpers; random sampling and `low_u64`; auxiliary canonical
integer bit/window/shift helpers; and the optional consumer-trait wrappers.
Proofs of the multiplication and inversion kernels do not automatically prove
these callers.

The first layer proves these routines for every valid input:

| Routine | Proven result, with `B = 2^64` |
| --- | --- |
| `adc` | Low remainder and high quotient of `lhs + rhs + carry` |
| `mac` | Low remainder and high quotient of `lhs * rhs + accumulator + carry` |
| `sbb` | Borrow at most one and `low + rhs + borrow = lhs + B * outgoing_borrow`, assuming incoming borrow at most one |
| `carry_add` | `low + B * outgoing_carry = lhs + rhs + incoming_carry` |
| `wide_mul` | Low remainder and high quotient of `lhs * rhs` |

These contracts include successful execution with overflow checks and debug
assertions enabled. The word-layer census checks 13 declarations, including
the supporting arithmetic identities and flag-disjointness proofs.

The second layer proves every shared multi-limb routine for arbitrary limb
values, including both of Common's new flag-carried chains. Write `val4` and
`val8` for the natural numbers represented by four and eight little-endian
limbs, and `R = B^4`:

| Routine | Proven result |
| --- | --- |
| `compare_limbs` | Returned ordering agrees with `val4` |
| `add_limbs` | `val4(out) + R * carry = val4(lhs) + val4(rhs)`, carry at most one |
| `subtract_limbs` | `val4(out) + val4(rhs) = val4(lhs) + R * borrow`, borrow at most one |
| `carry_add_limbs` | Exact addition identity with a Boolean carry |
| `borrow_sub_limbs` | Exact subtraction identity with a Boolean borrow |
| `multiply_wide` | `val8(out) = val4(lhs) * val4(rhs)` |
| `square_wide` | `val8(out) = val4(value)^2` |

The complete two-layer census checks 40 declarations, including the loop
unfoldings and integer bounds. These proofs use the actual production module
directly, with its debug assertions enabled.
The third layer proves every portable Montgomery kernel, including Common's
new split-product multiplier and flag-carried modular addition and subtraction.
Write `p` for the selected modulus:

| Routine | Input bound and proven result |
| --- | --- |
| `reduce_once` | Below `2p`; result is `input mod p`, below `p` |
| `reduce_twice_modulus` | Five-word input below `4p`; result is `input mod 2p`, below `2p` |
| `add_twice_modulus`, `_rust` | Both inputs below `2p`; their sum modulo `2p`, below `2p` |
| `sub_twice_modulus`, `_rust` | Both inputs below `2p`; result plus `rhs` agrees with `lhs` modulo `2p`, below `2p` |
| `montgomery_reduce_unreduced` | `T < pR + p²`; result below `3p`, with `R·out = T + m·p` and `m < R` |
| `montgomery_reduce` | `T < pR`; canonical Montgomery result below `p` |
| `montgomery_multiply` | Both operands below `2p`, or product below `pR`; result below `2p`, with `R·out = lhs·rhs + m·p` and `m < R` |
| `montgomery_multiply_loose`, `_rust` | Both operands below `2p`; the same exact Montgomery equation and result bound |
| `montgomery_square` | Input below `2p`; the Montgomery square equation and result below `2p` |
| `square_run` | Every `usize` count and either final-factor branch; loose bounds and the weighted power congruence |

The fast multiplier's proof checks every wide product and split carry chain,
the omitted cancelled low product, all three zero-carry assertions per round,
both public input-bound assertions and the four-round composition. The existing
Pasta closure theorem gives the sharper result bound below `2p`.
Repeated squaring proves `R^(2^n-1)·out ≡ value^(2^n) mod p` without a factor,
and `R^(2^n)·out ≡ value^(2^n)·factor mod p` with a factor.

The harness imports production `word.rs` and `montgomery.rs` and derives its
concrete prime dictionaries from the pinned `parameters.rs`. Lean checks their
modulus shape, inverse, doubled modulus and closure inequalities.
[KernelBridge.lean](proofs/KernelBridge.lean) proves the definitional agreement
of every shared word and limb routine with the direct production extraction.
The complete three-layer census checks 124 declarations.

The fourth milestone connects the core native APIs to ordinary integers modulo
both Pasta primes. Define `decode(limbs) = val4(limbs) · R⁻¹ mod p`; Lean checks
the two concrete radix inverses independently of the implementation.

| Native API | Proven result |
| --- | --- |
| `mul`, `square` | Decoded multiplication and squaring modulo `p` |
| `add`, `sub`, `neg`, `double` | Decoded arithmetic modulo `p` |
| `triple`, `mul_by_4`, `mul_by_8` | Decoded scaling modulo `p`, with a stored result below `p` |
| `half` | Decoded division by two for loose and reduced values, preserving the representation bound |
| `mul_add`, `mul_sub` | Decoded composed arithmetic modulo `p` |
| `from_u64`, `from_u128`, `from_i64` | Exact integer embeddings, including the minimum signed input |
| `pow_u64` | Decoded exponentiation for every 64-bit exponent |
| `invert` | For loose and reduced inputs, `None` exactly for decoded zero; otherwise a canonical decoded inverse |
| `reduce`, `into_loose` | Canonical stored representative and widening, with decoded value preserved |
| `ZERO`, `ONE`, `is_zero`, `is_one` | Correct identities and zero recognition in the loose representation |
| Montgomery import/access | Limb preservation under the stated representation bound |
| `from_wide_bytes_reduced` | Reduction of every 64-byte little-endian integer modulo `p`, in both representation states |
| `from_bytes_reduced` | Reduction of every finite little-endian byte slice modulo `p`, in both representation states |

The extraction wrapper calls 86 concrete Fp/Fq entry points. The proofs also
cover the explicitly selected private generic halving routine, the reduced
constructor, reduced `from_u64`, already-reduced
`reduce`, and native `square_run` for every count and either factor branch.
Arithmetic and imported loose values assume their documented stored bound
below `2p`; reduced values assume the bound below `p`. These are explicit
proof hypotheses, rather than checks on arbitrary POD bytes.
[NativeBridge.lean](proofs/NativeBridge.lean) connects the actual production
native kernels to the generic harness. Constructors and multiplication use
Common's fast loose multiplier, while the portable addition and subtraction
use its flag-carried modular kernels. The current complete census includes
every supporting native theorem and parameter proof alongside the additional
APIs described below.
Native arithmetic and parity declarations use only Lean's three standard axioms.
Specified codec and unrestricted integer-conversion declarations also retain
Aeneas's abstract `Formatter` type through Rust debug and unwrap signatures.
Each type-only dependency is listed individually in the census catalog.

The root-of-unity APIs cover every 32-bit logarithmic size: sizes above 32
return `None`; accepted sizes return the canonical stored table entry with
primitive order `2^log_size`. The forward value is
`5^((p - 1) / 2^log_size)` modulo the prime. Its inverse has the same primitive
order and their product is one. Loose and reduced Fp/Fq contracts are included.

The default square-root path proves `sqrt`, `sqrt_alt` and `sqrt_ratio` for both
fields and all valid reduced inputs. The contracts distinguish residues and
nonresidues, prove the returned root's equation and stored bound, and cover
zero inputs and zero denominators. The proof checks the fixed exponentiation
chains, primality certificates for both Pasta moduli, the root tables,
Tonelli–Shanks termination and correction invariants, and all six public APIs.
The optional `sqrt-table-large` path covers the same six public APIs and zero
cases. Lean checks the 897 stored powers per field and every inverse-table
lookup used by the order-256 subgroup. The proof follows canonical hash
lookup, four-byte subgroup exponent recovery, table indices and products,
the rounded half exponent, square flags and final reduction. The separately
extracted public callbacks invoke the extracted native exponentiation and
large-table implementations through their four-limb representations.

The 64-byte decoder proves the exact eight-limb iterator sum of its two raw
products, discharges its final zero-carry assertion, and connects REDC to the
independent little-endian integer of the input. The constants and bounds for
both Pasta moduli are checked in Lean.

The arbitrary-length decoder covers empty inputs, zero-padding to 32 or 64 bytes,
and the reverse-chunk Horner loop for longer slices. The proof handles the initial
partial chunk, proves all remaining chunks have 32 bytes, and shows that every
iteration decreases the unconsumed length. Its invariant connects the stored
Montgomery result to the independent little-endian integer of the entire slice.

The deferred `ProductSum` accumulator proves all six public operations for
both fields. Its decoded value is the integer stored by all nine words times
`R⁻²`, reduced modulo the field prime:

| Operation | Proven decoded result |
| --- | --- |
| `new` | Zero |
| `add_product` | Previous value plus the product of the decoded inputs |
| `add_square` | Previous value plus the decoded input squared |
| `add_term` | Previous value plus the decoded input |
| `merge` | Sum of both accumulator values |
| `finish` | The accumulator value, with the returned stored limbs below `2p` |

The contracts cover every nine-word accumulator state and every limb value
of each generic field operand. Partial reduction, the overflow correction,
its seven ADCs and final zero-carry assertion, the sixteen-MAC product chain,
the eight-ADC square and merge chains, and final REDC are included. The bounded
internal product helper also proves exact integer accumulation whenever its
stated `B^9` input bound holds. These contracts place no limit on the number
of public accumulator updates. Complete portable and AArch64 slice sums are
also proved below, together with the array and iterator wrappers. The AArch64
Comba helpers prove exact three-word product-column addition, initialization
and merging of four column values. The complete block proof discharges their
`B^3` bounds and connects all seven columns to the original product sum.

The signed product-difference contracts prove `mul_sub_product` computes
`a*b - c*d` and `mul_sub_double_product` computes `a*b - 2*c*d`, modulo the
selected Pasta prime. They cover both fields and all combinations of loose
and reduced operand states, under each state's documented stored bound.
The result is loose and stored below `2p`. The proofs check all eight doubling
and subtraction words, the outgoing borrow, the selected `p`, `2p` or `3p`
restoration offset, all four corrected upper words, carry cancellation,
optional high-half folding and the final Montgomery reduction.

The signed-62 inversion helpers prove that `to_signed62` preserves every
input digit, `pack62` preserves the represented integer for inputs below
`2^255`, and `unpack62` reverses canonical packing exactly. The packing and
unpacking assertions are included. On the pinned AArch64 target, the
`negative_eta_multiplier` proof covers every odd bottom word and each
low-bit mask of width zero through six: its output is within the mask and
makes `g + f*w` divisible by `2^width`. The proofs connect the actual wrapping
multiplications, subtraction and mask to the integer cancellation identity.
These helpers establish the representation and one accelerated divstep
formula. The complete public inversion proof composes them with the signed
updates, coefficient bounds, bounded outer loop and convergence certificate
described in the later inversion milestones.

[CommonFG62Update.lean](proofs/CommonFG62Update.lean) additionally proves
`update_fg_62_var` for every active length from one through five. For each
matrix row, `2^62` times the represented output equals the corresponding
linear combination of the two represented inputs. Lower active digits are
normalized and inactive limbs are unchanged. The proof includes the iterator
exhaustion and all checked operations. Its hypotheses require bounded active
digits, bounded matrix rows and cancellation of the bottom 62 bits. The batch
proof below establishes the matrix bounds and cancellation; the complete
public inversion proof discharges the caller's input-digit hypotheses.
[CommonFG62FirstUpdate.lean](proofs/CommonFG62FirstUpdate.lean) proves the
sparse first-batch specialization, including both shifted sparse terms and
the omitted zero term. Under the modulus-shape and input contracts it returns
exactly the same limbs as the generic five-limb update. It also proves the two
full signed-integer row equations and normalized lower digits.

[CommonDivstepOdd.lean](proofs/CommonDivstepOdd.lean) proves both native
cancellation branches and the guarded odd loop body. Supporting proofs cover
the sentinel trailing-zero count, checked shifts and eta updates, mask widths,
word/integer congruences, integer divstep blocks and transition-matrix
composition. [CommonDivstepFull.lean](proofs/CommonDivstepFull.lean) connects
the complete native loop to exactly 62 integer divsteps. It proves successful
execution, the exact transition matrix and eta, determinant `2^62`, and both
row bounds. The result holds for full signed integers whose low 62 bits match
the input words, with odd initial `f` and `|eta| ≤ 683`. The direct
`CommonDivsteps` extraction uses fully defined
models for the lossless `u32` to `i64` conversion and Rust's `trailing_zeros`
intrinsic. Absolute value, wrapping negation and range containment reuse the
existing models; the relevant pinned standard-library sources are hashed in
`provenance.json`.

Common's signed-divsteps inversion implementation is proved directly, including
its convergence and public contracts for loose and reduced Fp/Fq inputs.
The old Udon inversion proof is not used as evidence for the changed routine.
The optional `aarch64-asm` implementation is outside this package's scope.

The canonical codec proofs cover both loose and reduced values of each field:
integer conversion rejects exactly the inputs at or above the prime; byte
conversion uses the independent little-endian integer of all 32 bytes; and
canonical bytes round-trip exactly. Encoding followed by decoding preserves
the decoded field value. Unrestricted 256-bit integer conversion computes
reduction modulo the prime. Parity reads bit zero of the decoded canonical
representative. Supporting contracts and all public endpoints are included
in the census.

## Standard-library model boundary

Aeneas does not yet supply models for `u64::carrying_add` and
`u64::borrowing_sub`. [word_support/FunsExternal.lean](word_support/FunsExternal.lean)
provides transparent definitions matching the pinned Rust standard-library
bodies: two overflowing operations, a Boolean-to-word conversion, and an OR of
the two flags. [WordPrimitives.lean](proofs/WordPrimitives.lean) proves the exact
integer results and that the flags cannot both be set. The latter discharges
the precondition of Rust's `disjoint_bitor` intrinsic and justifies ordinary
Boolean OR in the models. These are definitions with checked proofs, not
arithmetic axioms. Their agreement with the standard-library bodies is an
explicit translation boundary; the Rust source file is pinned and its hash
is checked during replay.

Common's small multipliers and halving use mutable array iteration and a mutable/owned
Zip rather than an indexed loop. Transparent models implement array
`IntoIterator`, owned iteration in index order, and mutable Zip with Aeneas's
existing `IterMut.next` borrow reconstruction. The source files implementing
these operations and their iterator specializations are pinned during replay.
The model uses value/index state, rather than Rust's pointer and uninitialized
storage representation; its operational agreement with Rust remains an
explicit standard-library translation boundary. These models are used only
for four- and eight-limb, equal-length `u64` iterations in the current native proofs.
Codec models also provide ascending, state-threaded `array::from_fn`,
conditional `bool::then`, `Option` equality, and mutable eight-byte chunks.
The codec proofs check all four callbacks and all four writes. The chunk
model preserves the original full slice and uses an index to represent the
remaining chunks; a returned chunk's writes are reconstructed into that slice.
These proofs use 32-byte slices and eight-byte chunks. Agreement with Rust's storage layout and optimized Zip specialization remains the same explicit
standard-library translation boundary.

Arbitrary-length decoding adds a transparent read-only `Chunks` model. It retains
the unconsumed slice and nonzero chunk size; `next_back` first returns the final
partial chunk, then full chunks. Aeneas's existing `Rev` model supplies reverse
iteration. The pinned Rust sources include the marker, reverse iterator and
iterator trait implementations. [NativeChunks.lean](proofs/NativeChunks.lean)
checks chunk lengths and byte-value decomposition; [NativeBytesLoop.lean](proofs/NativeBytesLoop.lean)
proves the Horner invariant and termination; [NativeBytesCaps.lean](proofs/NativeBytesCaps.lean)
connects it to both fields and representation states.

Aeneas retains the decoder loop's `ReductionState<S>` dictionary but incorrectly
drops its type parameter `S`. [retain_loop_type.py](adapters/retain_loop_type.py)
adds one inert zero-sized `PhantomData<S>::clone` to keep that type in the loop
term, then makes its type argument explicit in Lean. Rust's pinned marker clone
returns the same marker; its transparent model and inertness proof do likewise.
The adapter adds three locals and nine statements, preserves every original
instruction, and requires that reversing the addition restore the entire original
AST. This workaround is an explicit translation boundary.

Aeneas's ordinary `Iterator` dictionary does not carry the backward function
needed by mutable iteration. [model_mutable_iterators.py](adapters/model_mutable_iterators.py)
replaces its mutable dictionary with the transparent model and specializes
exactly ten limb Zip constructors and eighteen limb Zip `next` calls, plus one
byte-chunk constructor and one byte-chunk `next` call. A reverse
comparison checks that all other generated code is identical; immutable Zip
calls are preserved. [NativeSmallLoop.lean](proofs/NativeSmallLoop.lean) proves
that the actual outer loop equals its explicit four-MAC expansion, including
all borrow write-backs. [NativeSmallRepair.lean](proofs/NativeSmallRepair.lean)
proves the four-ADC repair loop, its final carry bound and exact integer sum.
[NativeSmallReduction.lean](proofs/NativeSmallReduction.lean) then proves the
Pasta-specific fold and conditional repair; [NativeSmall.lean](proofs/NativeSmall.lean)
connects it to all six public small-multiplier APIs.
[NativeHalfLoop.lean](proofs/NativeHalfLoop.lean) proves the parity-masked
four-ADC halving loop and borrow reconstruction; [NativeHalf.lean](proofs/NativeHalf.lean)
proves its carry vanishes, its output is even before shifting, and the decoded
result is division by two for both fields and reduction states.
[NativeWideAdd.lean](proofs/NativeWideAdd.lean) proves the eight-ADC loop used
by wide decoding, including every mutable writeback and the exact outgoing carry.

The accumulator's merge loop hits an Aeneas limitation when joining nested
mutable/shared Zip borrows. [unroll_merge.py](adapters/unroll_merge.py) expands
the actual LLBC loop into nine iterations: eight payloads and an exhaustion
check. An independent structural checker compares every copied instruction,
branch and original continuation, verifies that every other declaration and
AST field is unchanged, and rejects four mutations during replay. A false
assertion bounds the expansion. [NativeProductMergeBound.lean](proofs/NativeProductMergeBound.lean)
checks the iterator bound and exhaustion; [NativeProductMergeExpansion.lean](proofs/NativeProductMergeExpansion.lean)
proves the generated merge equals the eight-word ADC composition, discharging
the added guard. [NativeLoopExpansion.lean](proofs/NativeLoopExpansion.lean)
proves that a successful finite loop expansion gives the same result as the
unbounded loop. The adapter's agreement with LLBC control-flow semantics remains
an explicit translation boundary; this is not a verified compiler transformation.
Common's production Rust loop is unchanged. Mutable slice `IntoIterator` uses
the pinned iterator operations and the same transparent borrow reconstruction.

The signed-62 f/g update has the same loop-join limitation.
[unroll_fg62.py](adapters/unroll_fg62.py) retains five actual iterator calls:
four possible payloads and the exhaustion check. Its independent checker
compares every copied instruction and continuation, restores the complete
original AST and rejects four mutations. An additional failure guard bounds
the expansion. The five Lean length-specific contracts discharge that guard
and prove equality with the checked row compositions. The adapter remains
part of the translation trust boundary; the production Rust is unchanged.
The only supplied external operation reuses the already-defined
`RangeInclusive::contains` model.

The product-difference loops also contain exhaustion continuations with nested
returns that Aeneas cannot translate. [hoist_product_difference_exits.py](adapters/hoist_product_difference_exits.py)
moves exactly three intact continuations past their loops and leaves a `Break`
in each exhaustion branch. Reversing the movements must restore the complete
original AST; the checker rejects four mutations during replay. Agreement with
LLBC control-flow semantics remains an explicit translation boundary.
[apply_difference_back.py](adapters/apply_difference_back.py) then applies two
generated mutable Zip backward functions to their original iterator seeds.
Its reverse comparison preserves all other generated text.
[NativeProductSubtractLoop.lean](proofs/NativeProductSubtractLoop.lean) proves
all eight resulting writes and the exact subtraction equation;
[NativeProductRestoreLoop.lean](proofs/NativeProductRestoreLoop.lean) proves
the upper-slice restoration and the unchanged lower half. These adapters
preserve production Rust and add no arithmetic axioms.

The square-root extraction also uses a transparent `RangeInclusive::contains`
model matching the pinned Rust range-bound checks, including exhausted ranges.
[copy_bool_assertions.py](adapters/copy_bool_assertions.py) changes only scalar
Boolean assertion operands from `Move` to `Copy`, preserving every assertion
and branch. This avoids Aeneas reading a concrete moved Boolean twice. The
adapter checks exactly two generic and eight native occurrences, reverses the
changes, and requires equality of the entire original AST. An unused cyclic
dictionary back edge is projected while preserving all bodies, types, globals
and exponentiation callbacks. Callback models invoke the extracted native
exponentiation functions whose arithmetic schedules are proved in Lean.

The remaining translation boundary includes Rust/Charon/Aeneas, the supplied
primitive models and Lean's kernel. The axiom census accepts only `propext`,
`Classical.choice` and `Quot.sound`, plus the exact type-only `Formatter`
declaration for the specific debug-formatting paths listed in the catalog.
This is an abstract formatting type, not an arithmetic assumption. The per-declaration allowances
are in [catalog.json](catalog.json). The census rejects errors, missing
or duplicate declarations, `sorryAx` and arithmetic axioms. No proof uses
`native_decide`. The extracted model is also scanned for unfilled externals
and proof holes.

## Reproduction

Use the Aeneas release and prepared Lean backend pinned by
[provenance.json](provenance.json). The backend's Lean and Mathlib dependencies
must be installed, along with zsh, Rust `nightly-2026-09-17` and its `rust-src`
component. `AENEAS_TOOL_ROOT` below denotes the unpacked release directory
containing `aeneas`, `charon` and `backends/lean`.

```console
python3 qa/aeneas/build_native_charon.py --archive "$CHARON_SOURCE_ARCHIVE" \
  --output target/aeneas/native-charon --offline
python3 qa/aeneas/reproduce.py --tools "$AENEAS_TOOL_ROOT" \
  --native-charon target/aeneas/native-charon \
  --output target/aeneas/native-check --offline
```

The portable product-sum extraction also requires the target standard library:

```sh
rustup target add x86_64-apple-darwin --toolchain nightly-2026-09-17
```

Each run requires a new output directory. It checks the production source,
tool binaries, versions and Rust standard-library source; performs fresh
extraction; compiles every model and proof; and checks the complete census.
The output includes stage commands, exit codes, timings, source/model hashes,
logs and a `results.json` record. `--prepare-only` records
`proofs_checked: false` and makes no proof-validation claim.

## Recovery baseline and milestone history

The counts and pending obligations in this section describe each recorded
milestone at the time it was completed. The current scope is stated at the
top of this README and in [CHECKLIST.md](CHECKLIST.md).

The original Git objects and milestone evidence were lost when the previous
checkouts disappeared. This recovery rebuilds the proof sources and extraction
scripts from the recorded edits and regenerates omitted model inputs with the
pinned compiler recipe. The restored package passed fresh extraction, Lean compilation and an exact
axiom census; historical timing records are not reused.

The recovery baseline at `9b7e711` is recorded in
[evidence/fresh.json](evidence/fresh.json): 40 successful fresh extraction
stages followed by 197 successful model/proof compilation stages after resolving
the dependency cache setup and restoring missing source edits. The earlier setup
failure is retained in the record. All 252 production source hashes, 29 model
hashes and 168 proof source hashes were checked again before saving the evidence.
[evidence/fresh.txt](evidence/fresh.txt) contains the full 836-declaration census.
The policy permits the three standard Lean axioms and exactly 39 named type-only
formatter exceptions; 38 of those exceptions occur in this run. It rejects
arithmetic axioms and `sorryAx`. No proof uses `native_decide`.

The five cumulative layer censuses (13, 40, 124, 256 and 529 declarations) also
pass separately. Their records are in [evidence/layers.json](evidence/layers.json).
At that recovery baseline, Common's complete inversion routine and public
slice/iterator product-sum dispatch were unproved. The subsequent milestones
below complete those paths.
The later incremental f/g update milestones add 54 declarations and check the
complete 890-declaration census. Their fresh helper extraction, proof compilation,
source hashes and remaining caller obligations are recorded in
[evidence/fg62-update.json](evidence/fg62-update.json) and
[evidence/fg62-first.json](evidence/fg62-first.json). A fresh replay of every
model and proof is still required after the remaining milestones.
The subsequent cancellation milestone adds 124 declarations in 25 proof modules
and checks the complete 1,014-declaration census. Its fresh direct extraction,
incremental compilation and exact axiom census are recorded in
[evidence/divsteps-foundations.json](evidence/divsteps-foundations.json) and
[evidence/divsteps-foundations.txt](evidence/divsteps-foundations.txt).
The complete native batch adds 16 declarations in six proof modules and checks
the complete 1,030-declaration census. See
[evidence/divsteps-batch.json](evidence/divsteps-batch.json) and
[evidence/divsteps-batch.txt](evidence/divsteps-batch.txt). Complete inversion
still requires coefficient updates, normalization and convergence of the outer
loop.
The coefficient foundations add 15 declarations in three proof modules and
check the complete 1,045-declaration census. They establish modular correction
and range mathematics plus checked comparator primitives. They do not yet
verify the native coefficient updates. See
[evidence/coefficient-foundations.json](evidence/coefficient-foundations.json).
`CommonInvHelpers` translates the remaining inversion helpers with checked
operations enabled. The supplied models define ordering equality, signed
wrapping negation, bitwise OR assignment and diagnostic display callbacks.
Display uses the backend's erased formatter model; its callbacks are outside
the successful arithmetic paths. The extraction of a helper is separate from
the proof of its complete contract.
[CommonActiveZero.lean](proofs/CommonActiveZero.lean) proves the native
`is_zero` helper for all active lengths 1 through 5. It returns true exactly
when all active digits are zero; for normalized lower active digits this is
equivalent to the represented active integer being zero. The milestone adds
nine declarations in three proof modules and checks the complete
1,054-declaration census. See [evidence/active-zero.json](evidence/active-zero.json).
[CommonCheckCompare.lean](proofs/CommonCheckCompare.lean) proves the complete
native debug comparison, including both scaling loops, normalization checks
and the descending digit scan. It agrees with integer comparison for active
lengths at most five, factors of absolute value at most two and the stated
digit bounds. Supporting proofs derive digit bounds and sign information
from normalized representations. This adds 24 declarations in nine proof
modules and checks the complete 1,078-declaration census. See
[evidence/signed-comparison.json](evidence/signed-comparison.json).
The coefficient carry support adds 31 declarations in nine proof modules and
checks the complete 1,109-declaration census. It covers the native input-range
assertion, sign and wrapping corrections, carry bounds, integer row equations,
and a proved equality between the general update's extraction and its factored
form. The complete coefficient-update contracts remain pending. See
[evidence/coefficient-carries.json](evidence/coefficient-carries.json).
Two new declarations require the backend's diagnostic formatter type, bringing
the exact named type-only allowances to 41. These allowances are recorded per
declaration in `catalog.json`; the arithmetic trust policy is unchanged.
The inversion-helper support module supplies a definitionally equal string
conversion with kernel-checked length bounds. This replaces the backend's
default native evaluation for diagnostic literals. `inv_string_model_eq`
checks that the string values agree with the original model.
[CommonCoeffUpdate.lean](proofs/CommonCoeffUpdate.lean) proves the complete
native general coefficient update, including its input and output assertions.
It returns normalized lower digits and coefficients in `(-2m, m)`, with
`2^62 * d' ≡ u*d + v*e (mod m)` and `2^62 * e' ≡ q*d + r*e (mod m)`.
The contract states the modulus, inverse, representation and matrix-row
preconditions explicitly. This milestone adds 12 declarations in six proof
modules and checks the milestone's 1,121-declaration census. The first-batch and
terminal specializations remain pending. See
[evidence/general-coefficients.json](evidence/general-coefficients.json).
Its two additional diagnostic-type dependencies bring the exact per-declaration
formatter allowances to 43.
The remaining proof milestones are tracked in [CHECKLIST.md](CHECKLIST.md).

The native first-batch coefficient update is also proved for normalized,
nonnegative input `e < m` and matrix rows with L1 norm at most `2^62`.
It succeeds with all runtime checks enabled, preserves `(-2m, m)`, returns
normalized lower digits, and satisfies both modular matrix-row equations
from the initial `d = 0`. See `evidence/first-coefficients.json`.

The native terminal coefficient update is proved under the same normalized
input, coefficient-range and row-norm bounds as the general update. All
three native coefficient paths now preserve their range and scaled modular
row equations, including the runtime assertions. Outer-loop convergence and public
inversion remain pending. See
`evidence/terminal-coefficients.json`.

Complete native `normalize_62` is proved for normalized input in
`(-2m, m)`: every checked word operation and debug assertion succeeds, the
output lies in `[0, m)`, and it is congruent modulo `m` to the input
negated exactly when the requested sign is negative. See
`evidence/normalization.json`.

Complete native `shrink_len` is proved for every active length 1 through 5.
It preserves both active integers and their digit invariants, and decreases
the length exactly when both top digits can be folded as sign extensions.
The update, coefficient, normalization and loop debug f/g range helpers
above are now proved. Complete bounded inversion and public inversion
remain pending. See `evidence/shrinking.json`.

The native debug f/g range assertion is proved with the loop
integer bounds. Supporting mathematics proves that divsteps preserve those
strict bounds, the first batch cannot terminate, terminal `f` is a unit,
and coefficient rows preserve the scaled Bezout equations. These are
foundations for the pending complete native outer-loop proof. See
`evidence/inversion-foundations.json`.

The narrow `invert_counted` model is now extracted with the existing
bounded f/g loop adapter; this remains part of the translation trust
boundary. Lean proves its helper bridges and the factored native general
batch, coefficient continuation, terminal arithmetic and shrinking steps.
The terminal contract returns canonical limbs satisfying
`x * out = 2^512 (mod m)`. Connecting the first batch and complete bounded
outer loop remains pending. See `evidence/inversion-batches.json`.

The next composition milestone proves the sparse first batch establishes the
full inversion invariant, including its nontermination assertion and coefficient
checks. The extracted outer-loop body agrees with the factored operations.
A decreasing-measure proof checks the inclusive Rust iterator and rules out its
failure branch under the explicit hypothesis that integer divsteps converge by
744 steps. Every successful result is canonical and satisfies the weighted
inverse equation, with a batch count between 2 and 12. The native zero-array
comparison is also proved. Connecting the complete entry routine and discharging
the convergence hypothesis remain pending. The strict census checks 1,242
declarations. See `evidence/inversion-composition.json`.

The complete extracted `invert_counted` entry is now connected to that
composition. For canonical input limbs, under explicit unit and convergence
hypotheses, it returns `None` exactly for zero; otherwise it returns canonical
limbs satisfying `x * out = 2^512 (mod m)` and a count from 2 through 12.
This includes packing, the first-batch assertion, all coefficient and range
checks, shrinking, and the inclusive loop. The convergence certificate and
concrete public Fp/Fq inversion contracts remain pending. The strict census
checks 1,245 declarations. See `evidence/inversion-entry.json`.

The public `PastaField::invert` method is also translated directly from the
production crate. Its f/g loop uses the existing structural adapter. The
parameter projection has an explicit generic mode that rejects concrete
implementations; it removes the unused dictionary cycle while preserving every
retained arithmetic body, type and compiled constant. A regression comparison
checks that the existing native projection produces the same document and
report as its committed predecessor.

Kernel-checked bridges connect the new model's helpers, outer loop and counted
entry to the proved core. The representation contracts cover reduction for
both states and the output's Montgomery bound check. Pure lemmas establish
that canonical nonzero inputs to a prime field are units, and that the
weighted inverse equation decodes to multiplication by one. All constants in
the existing production dictionaries are retained by the model conversion.
Concrete inversion-parameter instances and the complete public contracts remain
pending. This milestone checks 1,268 declarations. See
`evidence/public-inversion-foundations.json`.

The full convergence certificate now passes in the kernel. The untrusted
Python generator supplies 94,275 hull nodes and 1,321,785 vertices; Lean checks
all 1,467 generated modules. The soundness theorem covers every positive odd
modulus at most `2^255` and every input in `[0, m]`, proving convergence after
732 integer divsteps. Persistence of zero extends this to the implementation's
744-step limit.

The complete native outer loop and `invert_counted` entry now discharge their
convergence hypotheses. For canonical unit inputs, all checked operations and
debug assertions succeed, the final failure case is unreachable, and the result
is canonical with `x * out = 2^512 (mod m)` and a batch count from 2 through 12.
Zero returns `None`. The strict census checks 1,286 named declarations, including
the generated `all_steps_valid` aggregate and both convergence roots. Their
transitive axiom census covers all generated stage proofs; the declaration
count excludes individual generated node and stage declarations. See
`evidence/inversion-convergence.json`.

`reproduce.py` regenerates this certificate and checks both module families
before compiling the aggregate and the convergence theorem. Each independent
family uses two compiler workers, with serialized evidence recording; aggregate
roots and dependent proofs compile after their dependencies finish.

Public inversion is now complete for both Pasta fields and both input
representation states. The concrete signed-62 modulus, correction inverse and
Montgomery `R²` parameters are checked against the production dictionaries.
The public proof reduces the stored input, executes the verified core, checks
the returned Montgomery bound and follows the actual `Option` branches. It
returns `None` exactly for decoded zero; otherwise the canonical output's
decoded value multiplies the input to one modulo the prime. The existing
kernel-checked Pasta primality and radix inverses discharge the unit and decoding
requirements, and the checked certificate discharges convergence.

The dictionary conversion preserves all representation methods and flags;
phantom marker differences between extractions do not change the stored limbs.
The four public contracts are `fp_invert_loose_spec`, `fp_invert_reduced_spec`,
`fq_invert_loose_spec` and `fq_invert_reduced_spec` in
`proofs/CommonPastaInversionPublic.lean`. The strict census checks 1,303
named declarations. See `evidence/public-inversion-complete.json`.

The short product-sum slice paths now have complete public contracts for both
fields and all four pairs of input representation states. Empty slices return
zero; singleton slices use the verified multiplier; two- and three-product
slices accumulate the exact wide integer before the representation-dependent
high-half fold and Montgomery reduction. The result is a valid loose field
value whose decoded value is the sum of the decoded products modulo the prime.
Unequal lengths follow the original panic branch. These contracts require the
documented input bounds and equal lengths, with length at most three.

`CommonProductShort` is an explicit partial extraction of the public method:
the outside-scope branch is replaced with an existing panic. The structural
checker verifies its length guard, preserves every retained instruction and
signature, and restores the complete original AST for comparison. A second
checked adapter expands the eight-word mutable Zip loop, including its final
iterator exhaustion check. Lean connects that expansion to the proved adder,
discharges its guard, and proves the outer loop's invariant and termination.
The adapters remain part of the translation trust boundary. They do not verify
the long-slice, block, iterator or wrapper APIs.

The concrete contracts are `fp_sum_of_products_short_spec` and
`fq_sum_of_products_short_spec` in `proofs/CommonPastaProductShortPublic.lean`.
The strict census checks 1,341 declarations, with only the standard three Lean
axioms on the 38 new declarations. See `evidence/product-short.json` for the
fresh extraction and incremental proof evidence; it is not a complete replay
of the whole package.

### Portable serial slice sums

The x86_64 serial arm of `sum_of_products_slice`, for lengths 4 through 63,
now has complete public Fp/Fq contracts. The loop preserves the exact represented
integer sum and decreases the number of remaining pairs. The whole slice sum
fits nine words, so every bounded product helper's final overflow assertion
is discharged. Finishing returns loose limbs whose decoded value is the sum
of the decoded pairwise products modulo the relevant Pasta prime. Every pair
of production loose/reduced input states is accepted; this arm's proof needs
only the stored four-word bounds. Unequal lengths take the original panic.

`project_product_serial.py` checks the actual dispatch guards and replaces only
out-of-scope arms with an existing panic. Its checker restores the complete
input AST and rejects four mutations, including a changed retained loop.
Every retained arithmetic instruction, function signature, type and global
is unchanged. This is an explicit partial model; the theorem requires
`4 <= lhs.length < 64`. The generic accumulation-loop theorem itself permits
any initial accumulator and remaining sum whose total is below `2^576`.

Reproduction also requires the portable target's standard library:

```sh
rustup target add x86_64-apple-darwin --toolchain nightly-2026-09-17
```

The new contracts are in `proofs/CommonProductSerialAPI.lean` and
`proofs/CommonPastaProductSerialPublic.lean`. The strict census checks 1,369
named declarations and only the three standard Lean axioms on the 28 new
ones. `evidence/product-serial.json` records a fresh direct extraction,
byte-identical compiled models, the checked adapter and incremental proof
evidence. The four-lane arm, AArch64 block kernel and dispatch, remaining
wrappers, and complete fresh package replay remain pending.

### Complete portable slice sums

The portable `sum_of_products_slice` implementation is now proved at every
supported slice length for Fp and Fq and all four loose/reduced input pairs.
The proof covers short slices, serial accumulation, four independent lanes,
complete four-element chunks, trailing remainders, lane merging and the final
Montgomery reduction. Equal lengths and valid representation bounds are
explicit. Mismatched lengths execute the original panic.

Every accumulation and merge is exact as a nine-word integer. A slice has
fewer than `2^64` elements in the backend model, each product is below `2^512`,
and all partial sums are nonnegative and bounded by the full sum. These facts
discharge every internal overflow assertion. The resulting loose field value
decodes to the sum of the decoded pairwise products modulo the Pasta prime.

The pinned translator cannot join the two `ChunksExact::by_ref` borrows.
`model_product_chunk_borrows.py` models them with owned snapshots of the
read-only chunk iterators. Its checker verifies that the original iterators'
only later observations are two shared `remainder()` calls; advancing the
iterators preserves those remainders. The Lean partition, next-step and
paired-loop invariant proofs establish that frame. The checker permits only
these borrow/type/dictionary substitutions, checks the complete original AST
is recoverable and rejects four mutations. Arithmetic, guards, signatures,
globals and other function bodies are unchanged. This standard-library borrow
model is part of the translation trust boundary.

The fixed eight-word merge, eight-word short addition and four-lane mutable
loops retain every original instruction and continuation. Their independent
structural checks reject twelve mutations. Lean checks their correspondence
to the factored arithmetic and rules out every expansion guard. The transparent
mutable-iterator dictionary model retains all borrow reconstruction functions.

`proofs/CommonProductPortableAPI.lean` gives the complete generic contracts;
`proofs/CommonPastaProductPortablePublic.lean` gives the two concrete field
contracts. The strict census checks 1,438 declarations, with only the three
standard Lean axioms on the 69 new ones. `evidence/product-portable.json`
records a fresh direct x86_64 extraction, byte-identical compiled models,
all adapter checks and incremental compilation of twenty proof modules.
Iterator and array wrappers and a fresh complete package replay remain pending.


### Complete AArch64 slice sums

The direct `aarch64-apple-darwin` extraction now proves the complete Rust
32-product block kernel and public slice dispatch. Both concrete Pasta fields
and all four loose/reduced input pairs return a valid loose representation of
the decoded pairwise product sum. Equal lengths and documented representation
bounds are explicit. Unequal lengths follow the original panic branch.

The kernel proof accounts for all sixteen limb-product contributions, the
seven Comba columns, carry propagation, the final zero-high-word assertion and
the nine-word overflow assertion. Each column's three-word bound is discharged
for blocks of at most 32 pairs. Exact accumulation in the outer chunk loop and
the finite slice-length bound discharge the nine-word bound for every supported
slice. Empty, short and serial arms are included in the same extracted model.

`outline_product_blocks.py` lifts the sixteen unchanged macro expansions into
separate helpers so Aeneas can translate the repeated sequential loops. Its
inverse checker verifies captured-column routing, arguments, local-variable
renaming and lifetimes, restores the complete original AST, and rejects six
mutations. Only storage cleanup outside each new helper's scope changes on
unwind. The four-lane arm removed on this target requires contradictory length
guards; its checked adapter rejects four mutations and the corresponding Lean
lemma rules the arm out. Both adapters remain in the translation trust boundary.
Transparent models of standard shared `chunks` and `as_chunks` partitioning
include their tails and iterator exhaustion; Lean checks the partition facts
used by the block proof.

The strict census checks 1,535 declarations. The 97 new declarations in 25 proof
modules depend only on Lean's three standard axioms. A fresh extraction through
the exact replay-script block reproduces the four compiled model files. See
`evidence/product-aarch64.json` for incremental compilation, source/model hashes
and the full strict census. This is incremental evidence; the complete package
replay remains pending with the iterator and array wrappers.


### Complete product-pair iterators

`sum_of_product_pairs` is proved for Fp and Fq and all four production
loose/reduced input pairs. The contracts cover empty and short iterators, the
first four bounded updates, the unrestricted remaining loop and final
Montgomery reduction. Every ninth-word overflow is folded modulo the Pasta
prime, so the proof imposes no term-count bound. A valid loose result decodes
to the sum of decoded products in the actual iterator trace.

Generic iterators can fail or diverge. The contracts explicitly require a
successful `IntoIterator` conversion and a finite, error-free `next` trace
ending at its first `None`, together with the input representation bounds.
They do not certify an arbitrary iterator implementation's termination.

The pinned backend drops a collection parameter while retaining its iterator
parent projection. `project_pair_iterator.py` exposes that existing parent;
the public `sumOfPairs` view supplies exactly `IntoIterator.iteratorInst`.
The adapter changes no operation or control flow, restores the original AST
and rejects four mutations. `share_product_types.py` checks eleven complete
Rust type declaration blocks against the portable extraction before sharing
them through transparent aliases; four mutations are rejected. Both adapters
remain part of the translation trust boundary.

Kernel-checked equalities connect 69 common helpers to the portable model.
An additional execution equality connects the newly sequential overflow-fold
loops to the already proved fused-loop extraction. The native word contracts
then prove each multiply/carry step and every modular overflow correction.
`proofs/CommonProductPairsAPI.lean` contains the generic contracts;
`proofs/CommonPastaProductPairsPublic.lean` instantiates both Pasta fields.

The strict census checks 1,632 declarations. The 97 new declarations in nine
proof modules use only Lean's three standard axioms. A fresh direct x86_64
extraction through the replay-script block reproduces the four compiled model
files. `evidence/product-pairs.json` records the incremental compilation,
source/model hashes, adapter checks and complete census. Array and dot wrappers
and the fresh complete package replay remain on the checklist.


### Array and slice dot wrappers

The direct `sum_of_products` array wrapper and `products::dot` slice wrapper
now have Fp/Fq contracts for all four loose/reduced input pairs. Both return a
valid loose representation of the decoded pairwise product sum. Arrays share
a type-level size; slice `dot` explicitly requires equal lengths. A separate
contract proves the original panic for unequal slice lengths.

`proofs/CommonProductArrayDot.lean` connects both wrappers to the complete
portable slice proof. The strict census checks 1,639 declarations; the seven
new declarations use only Lean's three standard axioms. The directly extracted
wrapper bodies were already included in P4's three-root model and their hashes
are unchanged. `evidence/product-array-dot.json` records compilation, the full
census and the 66 unchanged baseline model hashes. `dot_iter` and the fresh
complete package replay remain pending.


### Complete iterator dot wrapper

`products::dot_iter` now has Fp/Fq contracts for all four loose/reduced input
pairs. Under successful conversion and length calls, finite error-free input
traces, correct reported lengths, equal input lengths and ordinary zip
construction, it returns a valid loose representation of the decoded dot
product modulo the prime. Separate theorems prove the original panic for
unequal reported lengths and for unequal actual lengths under correct reports.
The standard default zip construction is instantiated and checked. Another
contract describes the actual zipped trace when a caller overrides zip.

The pinned standard model omits the trait's `len` and `zip` method fields.
`ExactIteratorOps` preserves both Iterator supertrait dictionaries, both actual
length callbacks and the left actual zip callback. It does not silently replace
overrides with default bodies. `project_dot_iterator_operations.py` changes
only the two dictionary parameter types and that parent-method projection;
its inverse checker preserves all remaining text and rejects five mutations.
The emitted default-len template is unused by the model, and no implementation
or axiom is supplied for it.

Charon's associated-type lifting also leaves two redundant Iterator Item
variables. `project_dot_iterator_items.py` checks the two IntoIterator and
ExactSizeIterator supertrait paths for the same Rust Iterator Self type, then
uses Rust's unique associated Item to replace 37 type annotations. Arithmetic,
control flow and every other AST node are preserved; five mutations are
rejected. These checked coherence and dictionary projections remain in the
translation trust boundary. The eleven shared production type declarations
are checked against the portable model before transparent aliasing.

The 73 helper equalities reuse the complete product-pair implementation.
`proofs/CommonProductZipTrace.lean` connects finite input traces to standard
Zip iteration. `proofs/CommonProductDotIterAPI.lean` states the actual-operation
and conventional dot-product contracts;
`proofs/CommonPastaProductDotIterPublic.lean` instantiates the Pasta fields.

The strict census checks 1,723 declarations in 391 authored proof modules.
The 84 new declarations depend only on Lean's three standard axioms. A fresh
direct extraction through the exact replay-script block reproduces the four
compiled model files; the 66 previous model files are unchanged. See
`evidence/product-dot-iter.json` for the incremental evidence. Every arithmetic
and API checklist item is now complete; the full fresh package replay and
final scope-documentation pass remain pending.
