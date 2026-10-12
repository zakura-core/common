# Common Pasta field verification checklist

Work on `aeneas-common-field-verification`; commit each completed proof milestone
locally. Push only when explicitly authorized.

The starting point is `9b7e711`: 168 proof modules and 836 checked declarations.
The recorded extraction, compilation and axiom-census evidence is in
[`evidence/fresh.json`](evidence/fresh.json). A checked item below requires
successful Lean compilation and an updated strict census, not extraction alone.
Coverage is limited to the catalogued core Pasta and selected API paths below;
this is not a checklist of every API in Common's field module.

## Layers, bottom up

- [x] Words: exact word operations, carries, borrows and split products.
- [x] Multi-limb integers: comparisons, addition, subtraction, wide products and squares.
- [x] Montgomery arithmetic: reduction and the portable arithmetic kernels.
- [x] Fp/Fq operations: core arithmetic, representations and integer constructors.
- [x] Further APIs: codecs, byte reduction, roots, square roots, inversion and product sums.

The fifth layer already includes canonical encodings, arbitrary-length byte
reduction, roots of unity, default and large-table square roots, ProductSum
accumulator operations and signed product differences. Signed-62 packing,
negative-eta cancellation and basic Comba column helpers are also checked.

## Inversion

- [x] I1. Prove `update_fg_62_var` for every active length 1 through 5:
  exact matrix-row division by `2^62`, normalized output digits, inactive-limb
  preservation, successful checked operations and the stated input bounds.
- [x] I2. Prove the sparse first-batch `update_fg_62_first` specialization.
- [x] I3. Prove both cancellation branches and the complete `divsteps_62_var`
  batch, including its transition equations, determinant and row bounds.
- [x] I3a. Prove both native cancellation branches, masks, trailing-zero
  stripping and the guarded odd loop body; establish the supporting integer
  divstep and transition-matrix identities.
- [x] I3b. Connect all native loop iterations to exactly 62 integer divsteps
  and discharge the final determinant and row-bound assertions.
- [x] I4. Prove the general, first-batch and terminal coefficient updates,
  their modular equations and coefficient range preservation.
- [x] I4a. Prove the modular correction and coefficient-range mathematics,
  and the checked multiply/add/shift primitives of the debug comparator.
- [x] I4b. Prove the complete debug comparisons and all three native
  coefficient update routines using those facts.
- [x] I4b1. Prove the complete native debug comparison, including its
  multiplication and normalization loops, reverse scan and integer ordering.
- [x] I4b2. Prove the general, first-batch and terminal native coefficient
  updates and their debug range checks.
- [x] I4b2a. Prove the complete general coefficient update, including both
  output range assertions and the scaled modular row equations.
- [x] I4b2b. Prove the first-batch and terminal coefficient specializations.
- [x] I4b2b1. Prove the complete first-batch coefficient update.
- [x] I4b2b2. Prove the terminal coefficient update.
- [x] I5. Prove normalization, active zero detection and active-length shrinking.
- [x] I5a. Prove active zero detection, including its integer interpretation.
- [x] I5b. Prove active-length shrinking and normalization.
- [x] I5b1. Prove complete native coefficient normalization.
- [x] I5b2. Prove active-length shrinking.
- [x] I6. Prove the complete bounded inversion loop reaches its successful
  terminal case, preserves the scaled Bezout invariant and returns the
  Montgomery-form inverse. A finite Rust loop alone does not prove that the
  final failure case is unreachable.
- [x] I6a. Prove the debug f/g range assertion and the supporting integer,
  limb-bound, termination and scaled Bezout mathematics.
- [x] I6b. Check a convergence certificate for all 255-bit inputs in the kernel.
- [x] I6c. Compose the native first, continuing and terminal batches and prove
  the scaled Bezout invariant through the bounded loop.
- [x] I6c1. Prove the general native batch, coefficient continuation,
  terminal arithmetic and shrinking steps, and bridge their helper calls.
- [x] I6c2. Connect the first batch and native outer-loop body, and prove the
  bounded loop preserves the invariant and returns successfully under an
  explicit convergence hypothesis.
- [x] I6c3. Connect the `invert_counted` entry and discharge that convergence
  hypothesis with the complete kernel certificate.
- [x] I6c3a. Prove the complete native `invert_counted` entry under explicit
  input-unit and convergence hypotheses, including `None` exactly for zero.
- [x] I6c3b. Discharge convergence with the checked certificate.
- [x] I7. Connect the loop to public Fp/Fq `invert` for loose and reduced
  inputs: `None` exactly for zero, and a valid inverse otherwise.
- [x] I7a. Extract the public method; prove its core bridges, input/output
  representation checks and the decoding and input-unit lemmas.
- [x] I7b. Instantiate the concrete Pasta inversion parameters and prove the
  complete public contracts for both representation states.

## Product-sum APIs

- [x] P1. Prove the empty, singleton, two-product and three-product slice paths,
  including representation-dependent high-half folding and the final REDC.
- [x] P2. Prove portable slice accumulation, the four-lane path, chunk
  remainders and lane merging, with all accumulation bounds discharged.
- [x] P2a. Prove the portable serial slice arm for lengths 4 through 63,
  its exact bounded accumulation loop and final reduction for both fields.
- [x] P2b. Prove the portable four-lane arm, chunk remainders and lane merging.
- [x] P3. Prove the full AArch64 32-product block kernel and its slice dispatch,
  using the existing Comba helper contracts.
- [x] P4. Prove `sum_of_product_pairs`, including the short-iterator paths and
  the unrestricted accumulator loop.
- [x] P5. Connect array sums, `dot` and `dot_iter` to their implementations for
  both fields and all accepted reduction states. State equal-length input
  requirements explicitly and account for mismatched-length assertions.

- [x] P5a. Prove array sums and slice `dot` for both fields and all accepted
  reduction states, including `dot`'s mismatched-length panic.
- [x] P5b. Prove `dot_iter` with its actual length and iterator operations.

## Completed milestones

- I1 adds 41 declarations in 16 proof modules. The five length-specific
  contracts and their combined public helper contract compile. The updated
  census checks 877 declarations; the new declarations use only the three
  standard Lean axioms. See [`evidence/fg62-update.json`](evidence/fg62-update.json)
  for the incremental validation and the explicit remaining caller obligations.
- I2 adds 13 declarations in four proof modules, including equality of the
  optimized first-batch result with the generic five-limb update. The census
  checks 890 declarations. See
  [`evidence/fg62-first.json`](evidence/fg62-first.json).
- I3a adds 124 declarations in 25 proof modules. The complete strict census
  checks 1,014 declarations. This milestone establishes native branch and
  loop-body contracts before the complete batch proof in I3b. See
  [`evidence/divsteps-foundations.json`](evidence/divsteps-foundations.json).
- I3b adds 16 declarations in six proof modules. The native batch terminates
  and returns exactly the integer transition matrix after 62 divsteps, with
  the correct eta, determinant `2^62` and row bounds. The theorem also covers
  full signed integers agreeing with the input words modulo `2^62`. The census
  checks 1,030 declarations. See
  [`evidence/divsteps-batch.json`](evidence/divsteps-batch.json).
- I4a adds 15 declarations in three proof modules. These establish the
  correction's bottom-bit cancellation and strict `(-2m, m)` output range,
  and the comparator's checked arithmetic primitives. The complete native
  coefficient updates remain pending. The census checks 1,045 declarations.
  See [`evidence/coefficient-foundations.json`](evidence/coefficient-foundations.json).
- I5a adds nine declarations in three proof modules. For every valid active
  length 1 through 5, the native `is_zero` routine returns true exactly when
  all active digits are zero. With normalized lower active digits, this is
  equivalent to the active integer being zero. The census checks 1,054
  declarations. See [`evidence/active-zero.json`](evidence/active-zero.json).
- I4b1 adds 24 declarations in nine proof modules. The complete native
  `checks::mul_cmp_62` agrees with comparison of the represented integers,
  including its normalization assertions. Supporting bounds relate sign and
  digit bounds to active integer values. The census checks 1,078 declarations.
  See [`evidence/signed-comparison.json`](evidence/signed-comparison.json).
- Coefficient carry support adds 31 declarations in nine proof modules:
  the native coefficient-range assertion, sign and wrapping corrections,
  checked carry arithmetic, integer row equations, and equality between the
  extracted general update and its factored form. The complete native
  coefficient contracts remain pending. The census checks 1,109 declarations.
  Two added allowances cover the backend's diagnostic formatter type only.
  See [`evidence/coefficient-carries.json`](evidence/coefficient-carries.json).
- I4b2a adds 12 declarations in six proof modules. The native general update
  executes successfully, returns normalized lower digits, preserves
  `(-2m, m)`, and satisfies both matrix-row equations modulo `m` after
  multiplying the outputs by `2^62`. The census checks 1,121 declarations.
  See [`evidence/general-coefficients.json`](evidence/general-coefficients.json).

- I4b2b1 adds 19 declarations in five proof modules. The native first-batch
  specialization succeeds for normalized, nonnegative `e < m`, preserves
  the coefficient range and normalized lower digits, and satisfies the
  scaled matrix-row equations from `d = 0`. The census checks 1,140
  declarations. See [`evidence/first-coefficients.json`](evidence/first-coefficients.json).

- I4b2b2 adds seven declarations in four proof modules. The terminal
  coefficient update executes its single live row successfully, preserves
  normalized lower digits and `(-2m, m)`, and satisfies the scaled modular
  row equation. All three native coefficient update paths are now proved.
  The census checks 1,147 declarations.
  See [`evidence/terminal-coefficients.json`](evidence/terminal-coefficients.json).

- I5b1 adds 23 declarations in eight proof modules. Complete native
  normalization succeeds with all debug checks, preserves the signed input
  modulo `m`, and returns a normalized canonical value in `[0, m)`.
  The census checks 1,170 declarations.
  See [`evidence/normalization.json`](evidence/normalization.json).

- I5b2 adds ten declarations in five proof modules. The complete native
  shrinking routine preserves both active integers, normalized lower active
  digits, and active limb bounds for every length 1 through 5. It shrinks
  exactly when both top digits are sign extensions and the length is at
  least two. The census checks 1,180 declarations.
  See [`evidence/shrinking.json`](evidence/shrinking.json).

- I6a adds 13 declarations in five proof modules: the complete native f/g
  range assertion, strict integer range preservation by every divstep,
  active digit bounds, first-batch nontermination and terminal unit facts,
  and preservation of each scaled Bezout row. The complete native outer
  loop and public inversion remain pending. The census checks 1,193
  declarations. See [`evidence/inversion-foundations.json`](evidence/inversion-foundations.json).

- I6c1 adds 33 declarations in twelve proof modules. The narrow outer
  inversion extraction uses the existing structurally checked f/g adapter.
  Kernel-checked bridges connect its helpers to the earlier contracts.
  Factored native batch, continuation, terminal and shrinking steps preserve
  the loop invariants; the terminal output is canonical with
  `x * out = 2^512 (mod m)`. The first-batch and complete outer-loop
  connections remain pending. The census checks 1,226 declarations.
  See [`evidence/inversion-batches.json`](evidence/inversion-batches.json).

- I6c2 adds 16 declarations in nine proof modules. The first batch establishes
  the invariant and the native outer-loop body is connected. The bounded loop
  preserves the scaled Bezout invariant and succeeds with a batch count from
  2 through 12 under an explicit convergence hypothesis. The zero-array
  comparison is also checked. The complete entry connection and the kernel
  certificate that discharges convergence remain pending. The census checks
  1,242 declarations. See
  [`evidence/inversion-composition.json`](evidence/inversion-composition.json).

- I6c3a adds three declarations in three proof modules. The complete extracted
  `invert_counted` entry is connected under explicit unit and convergence
  hypotheses. It returns `None` exactly for zero, and otherwise a canonical
  weighted inverse with a batch count between 2 and 12. Convergence and the
  public Fp/Fq specialization remain pending. The census checks 1,245
  declarations. See [`evidence/inversion-entry.json`](evidence/inversion-entry.json).

- I7a adds 23 declarations in five proof modules and a direct public-method
  extraction. Native helper, loop and counted-entry bridges, representation
  checks, unit-input mathematics and decoded inverse mathematics pass. The
  parameter dictionary conversion retains all existing production constants.
  Concrete public inversion contracts remain pending. The census checks 1,268
  declarations. See
  [`evidence/public-inversion-foundations.json`](evidence/public-inversion-foundations.json).

- I6b and I6c3b add 18 census declarations in four authored proof modules
  plus the generated aggregate. Every one of the 1,467 generated certificate
  modules passes. The soundness framework proves convergence for all positive
  odd moduli at most `2^255` and inputs in `[0, m]` after 732 integer divsteps,
  hence by the native 744-step limit. The complete native loop and counted entry
  now discharge convergence and rule out their final failure case, preserving
  the canonical weighted inverse result for unit inputs. The census checks
  1,286 declarations and the generated aggregate's transitive dependencies.
  See [`evidence/inversion-convergence.json`](evidence/inversion-convergence.json).

- I7b adds 17 declarations in seven proof modules. Both concrete inversion
  parameter dictionaries are checked against the production constants. Public
  Fp/Fq `invert` now succeeds for all valid loose and reduced inputs, returning
  `None` exactly for decoded zero; otherwise it returns canonical limbs whose
  decoded value multiplies the input to one modulo the prime. The proofs use
  the existing kernel-checked primality and radix-inverse theorems and discharge
  convergence. The census checks 1,303 declarations. See
  [`evidence/public-inversion-complete.json`](evidence/public-inversion-complete.json).

- P1 adds 38 declarations in eleven proof modules. The short-slice contracts
  cover both Pasta fields and all four loose/reduced input pairs, returning
  a valid loose representation of the decoded sum modulo the prime. The proofs
  include exact accumulation, iterator exhaustion, carry checks, state-dependent
  high-half folding, REDC and the unequal-length panic. The model explicitly
  scopes the public method to lengths zero through three; longer paths remain
  pending. The census checks 1,341 declarations. See
  [`evidence/product-short.json`](evidence/product-short.json).

- P2a adds 28 declarations in five proof modules. A direct x86_64 production
  extraction covers the serial slice arm for lengths 4 through 63. A decreasing
  loop invariant proves exact accumulation below the nine-word limit; the
  concrete Fp/Fq contracts return a valid loose representation of the decoded
  sum. These contracts accept all four loose/reduced input pairs and need no
  limb bound beyond the stored four words. Mismatched lengths follow the
  original panic. The four-lane arm and AArch64 connection remain pending.
  The census checks 1,369 declarations. See
  [`evidence/product-serial.json`](evidence/product-serial.json).

- P2 completes portable slice dispatch for every equal-length slice admitted by
  the 32/64-bit backend model, including four lanes, exact chunks, trailing
  remainders and all lane merges. The concrete Fp/Fq contracts cover all four
  production reduction-state pairs. Checked invariants discharge every
  intermediate nine-word bound, and the final output has the decoded sum
  modulo the corresponding prime. The read-only chunk iterator adapter
  retains arithmetic and dispatch; its checker rejects four mutations and the
  proofs preserve the remainder frame. All three fixed-loop expansions are
  checked, including unreachable exhaustion guards. This adds 69 declarations
  in twenty modules; the census checks 1,438. See
  [`evidence/product-portable.json`](evidence/product-portable.json).

- P3 completes the AArch64 Rust block kernel and every public slice arm for
  both Pasta fields and all four reduction-state pairs. Exact column and block
  invariants discharge each three-word and nine-word bound, including both
  terminal carry assertions. The 32-element chunk and partial-tail model
  preserves the complete pairwise sum. Checked helper outlining retains every
  arithmetic payload and restores the original AST; its checker rejects six
  mutations. This adds 97 declarations in 25 modules; the strict census checks
  1,535. Fresh extraction reproduces all four compiled model files. See
  [`evidence/product-aarch64.json`](evidence/product-aarch64.json).

- P4 proves the complete public `sum_of_product_pairs` method for both fields
  and all four reduction-state pairs. It covers zero through three terms, the
  first four bounded updates, an unrestricted finite tail and final reduction.
  Every ninth-word overflow is folded modulo the prime. Contracts require a
  successful conversion and an error-free finite iterator trace, with valid
  input representations; they impose no term-count bound. The checked parent
  dictionary projection is reconstructed at the public boundary, and eleven
  byte-identical Rust type declarations are shared through transparent aliases.
  A kernel-checked execution equality connects the two overflow-loop exports.
  This adds 97 declarations in nine modules; the strict census checks 1,632.
  Fresh extraction reproduces all four compiled model files. See
  [`evidence/product-pairs.json`](evidence/product-pairs.json).

- P5a connects the directly extracted array sum and slice `dot` wrappers to
  the complete portable slice contracts for both Pasta fields and all four
  representation-state pairs. Equal array lengths follow from their common
  type-level size; slice `dot` requires equal lengths and has a separate
  mismatch-panic theorem. This adds seven declarations in one module. The
  strict census checks 1,639 declarations using the 66 unchanged model files
  already recorded in P4. See
  [`evidence/product-array-dot.json`](evidence/product-array-dot.json).

- P5b proves `dot_iter` for both fields and all four representation-state
  pairs, including both reported-length and actual-length mismatch assertions.
  Conventional dot products require successful conversions and length calls,
  correct length reports, equal finite input lengths, error-free `next` traces
  and ordinary zip construction. A separate contract handles the actual zipped
  trace when a custom zip method changes that behavior. The standard default
  zip constructor is instantiated and checked. The dictionary projection keeps
  actual callbacks, including overrides. Checked Iterator-item coherence changes
  only 37 type annotations; neither adapter changes arithmetic or control flow.
  The 84 new declarations in four modules use only Lean's three standard axioms;
  the strict census checks 1,723. Fresh extraction reproduces all four compiled
  model files. See [`evidence/product-dot-iter.json`](evidence/product-dot-iter.json).

## Final validation

- [x] V1. Record each completed milestone's source/model hashes, checked
  declarations and exact axiom census; keep unproved callers marked pending.
- [ ] V2. Run a fresh complete extraction and proof replay with the pinned
  toolchain, without proof holes or additional arithmetic axioms.
- [x] V3. Update the README, catalog and evidence to describe the final scope;
  commit each completed piece and leave the branch ready for the user to push.

The latest V2 attempt is incomplete: 1,380 module compilations passed,
including all 70 model files, all 733 certificate-data modules and 271 of 732
certificate-checking modules. Two checking processes exited 137 without Lean
diagnostics; the cause was not established. The final strict census was not
reached. The successful 1,723-declaration incremental census is recorded in
[`evidence/product-dot-iter.json`](evidence/product-dot-iter.json); the failed
fresh attempt is recorded separately in
[`evidence/full-replay-incomplete.json`](evidence/full-replay-incomplete.json).

## Outside this checklist

Other field paths remain unproved: batch inversion (including scaled/grouped
variants), FFT/butterfly kernels and power-of-two scaling, fraction-prefix and
power-fill routines, constant-prefix helpers, sampling and `low_u64`, auxiliary
canonical-integer bit/window/shift helpers and the optional consumer-trait
wrappers. Proving their arithmetic dependencies does not establish their
complete API contracts.

Elliptic-curve point operations, scalar multiplication, MSM, GLV, point
encodings, constant-time properties and the optional `aarch64-asm`
implementation require separate verification work.
