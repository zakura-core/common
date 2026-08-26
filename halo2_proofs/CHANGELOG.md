# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Prepared the `1.0.0-rc.4` release.
- Verifying-key generation now omits zero terms from sufficiently sparse fixed
  polynomial commitments and batch-normalizes fixed and permutation
  commitments.
- Advice-witness denominators now use the prover's two-lane batch inversion.
- IPA opening proofs now sample their zero-evaluation masking polynomial
  sparsely, as $\sum_t \alpha_t (X^{2^t} - x^{2^t})$, instead of sampling and
  committing a full domain-sized polynomial. The masking commitment is a
  $(k+2)$-term MSM, and the accompanying HVZK argument shows the revealed IPA
  scalar is either uniformly masked or publicly zero, exactly as with a
  full-width mask and with no exceptional witness-dependent challenge event.
- Added `Params::prepare_commitments`: builds prepared fixed-base multiexp
  tables over `[g..., w, u]` (shared with `prepare_zero_checks`) and
  `[g_lagrange..., w, u]`; when armed, `Params::commit` and
  `Params::commit_lagrange` evaluate through them on pools of at most eight
  effective threads (measured 1.2-1.8x per commitment at 1-8 threads on
  x86-64 and Apple silicon, across full-width and witness-like coefficient
  distributions) and keep the planned multiexp on wider pools, so arming is
  never a pessimization.
- Proof witness collection now stores advice numerators directly and retains
  only rational denominators for batched inversion.
- IPA opening proofs now keep late generator-fold rounds parallel instead of
  forcing chunks of at least 32 points.
- Lookup grand-product preparation now reuses its fraction buffer for product
  accumulation, avoiding one domain-sized allocation per lookup argument.
- Permutation grand-product preparation now reuses its fraction buffer for
  product accumulation, avoiding one domain-sized allocation per column set.
- Parallel polynomial evaluation now uses eight chunks per worker for finer
  load balancing across uneven evaluator workloads.
- Proof creation now prepares independent commitments and polynomial transforms
  concurrently, and batches transcript-adjacent polynomial evaluations while
  preserving proof randomness and transcript ordering.
- Quotient evaluation now shares repeated factors across non-consecutive
  constraint terms while retaining their original challenge powers.
- IPA opening proofs now compute independent round terms in parallel and fuse
  the blinding and value terms into each round commitment's multiscalar
  multiplication.
- Public-instance commitments and polynomial transforms for independent proof
  circuits are now prepared in parallel when multicore support is enabled,
  while retaining transcript order.
- Added an opt-in (default-off) `orbits` feature (forwarding `pasta_curves/orbits`)
- Permutation product polynomials for independent proof circuits are now
  prepared in parallel when the worker pool has capacity for both outer
  circuit tasks and their nested commitment and transform work.
  gating the prepared zero-check integration below. Built without it,
  `Params::prepare_zero_checks` is a no-op returning `false` and
  `MSM::eval` always evaluates the plain multiexp, so the machinery can
  be switched off — or later removed — without touching callers.
- `Params::prepare_zero_checks` builds and caches a prepared fixed-base
  zero-check over the SRS (`g`, `w`, `u`; see pasta's `glv::zero`), and
  `MSM::eval` then routes the verifier's final identity test through it,
  with the proof-specific commitment terms as the check's extra terms.
  It returns whether a prepared check was actually armed: `false` when
  the curve has no prepared backend, when the backend declines (its table
  for this SRS would exceed its internal memory budget — very large `k`),
  or without the `orbits` feature; verification then simply keeps the
  plain multiexp. Preparation is explicit (hundreds of milliseconds and
  tens of MiB at typical `k`, amortized across every verification with
  those params; batch verification pays one prepared check per batch), is
  never serialized, and is shared with all clones of the params. The
  routing is thread-aware: `MSM::eval` uses the prepared check on pools
  of at most eight effective threads — where the prepared final check
  measured ~1.5-2.4x faster on the Pasta curves at `k = 11` scale, and
  armed verification won by 8-22% end to end at 4-8 threads — and falls
  back to the plain planned multiexp on wider pools, where the prepared
  evaluation stops scaling while the unprepared planner keeps scaling
  (before the gate, armed verification measured 14-16% slower end to end
  on a 16-thread pool and 22-27% slower on a 32-thread pool), so arming
  is never a pessimization. Since the prepared check runs the
  accumulated commitment terms as their own planned MSM, `MSM::eval`
  also uses it only while those terms do not outnumber the fixed bases
  (the measured crossover on Ironwood batch validation), instead of the
  earlier half-the-fixed-bases cutoff.
- Proving keys now retain reusable floor-planning data produced during key
  generation. V1 proof creation consumes the cached layout instead of
  measuring and positioning the circuit again.
- **Breaking:** `create_proof` and `keygen_pk` now require a `Sync` circuit
  type with a `Send` configuration, and `FloorPlanner::synthesize_batch`
  carries matching `Send`/`Sync` bounds. Compatible floor planners, including V1, synthesize
  independent circuit witnesses in parallel when the `multicore` feature is
  enabled; the serial default remains for other planners.
- The V1 floor planner now measures and positions a circuit once when creating
  a proof for several instances of that circuit, then reuses the layout for
  each witness assignment.
- `FloorPlanner::synthesize_batch` now borrows the global-constant columns and
  debug-asserts the assignment/circuit pairing instead of reporting a caller
  bug as a synthesis error.
- Independent lookup grand-product polynomials and commitments are now
  prepared in parallel across circuits while preserving proof randomness and
  transcript ordering.
- Independent lookup arguments now prepare their permutation polynomials and
  commitments in parallel while preserving proof randomness and transcript
  ordering.
- Polynomial evaluation now indexes common-subexpression candidates by
  structural fingerprints, avoiding quadratic candidate scans while retaining
  exact structural matching.
- Proof creation now borrows existing value and coset polynomials when
  registering them with polynomial evaluators, avoiding redundant
  domain-sized clones.
- Lookup permutation construction now sorts input and table values concurrently
  and merges them, reducing Orchard prover time in one- and four-Action
  benchmarks.
- IPA generator folding now uses smaller parallel chunks during later rounds
  while retaining affine same-scalar multiplication batching.
- Single-worker Pasta multi-opening polynomial folds now interleave two wide
  product accumulators, shortening dependency chains while sharing cached
  challenge-power loads.
- Batch verification now merges arbitrary final-MSM terms in a contiguous
  buffer and canonicalizes them once, while retaining positional accumulation
  for the IPA generator coefficients.
- Multi-opening polynomial collapse now partitions coefficient ranges by
  estimated field-operation work in one parallel scope. Single-worker Pasta
  folds use cached challenge powers with wide-product accumulators.
- Multi-opening proofs now collapse polynomials in place, avoiding per-query
  polynomial allocations and separate multiplication and addition passes.
- Proof creation now evaluates independent coefficient-form polynomials in
  parallel, reusing common-point power tables and Pasta wide-product
  accumulators.
- Removed the `indexmap` dependency. The multi-opening argument now
  deduplicates commitments with a first-seen-order `Vec` plus a std `HashMap`
  index, preserving the exact iteration order (and therefore proof bytes)
  with O(1) lookups.

- The V1 floor planner now caches consecutive region-column writes, avoiding
  repeated hash-table lookups during circuit measurement.
- Independent polynomial transforms are now parallelized during proving-key
  generation and proof creation.
- Proving keys now retain and reuse FFT twiddles for fixed, permutation,
  advice, instance, lookup, and quotient transforms. At Orchard's `k = 11`,
  the cache is 288 KiB and cloned proving keys share its allocations.
- Added a test running `best_multiexp` at GLV-selected sizes inside explicit
  one- and three-thread Rayon pools, and a dedicated halo2 CI job that runs the
  multiexp tests with `multicore`, so the parallel Pasta multiscalar path is
  exercised by this crate's own suite.
- Pasta-curve parameter generation now uses the affine GLV curve FFT and
  enables its layer-level parallelism through the `multicore` feature. For
  Orchard's `k = 11`, `Params::new` measured 3.4x faster single-threaded and
  4.8x faster with all cores on Apple aarch64.
- Prepared the `1.0.0-rc.3` release.
- `Params::new` now normalizes its inverse curve FFT with parallel batched GLV
  scalar multiplication over the already-affine generators, reducing Orchard
  `k = 11` parameter generation by 7–9% on Apple aarch64.
- The `k = 9`, `k = 10`, Orchard-sized `k = 11`, and `k = 12` Lagrange
  commitment bases are now hash-pinned so curve-FFT optimizations cannot
  silently change the bases used by verification keys.
- The permutation- and lookup-argument provers' full-column batch inversions now
  go through a shared `batch_invert_multi` helper that splits the Montgomery
  prefix-product and back-substitution chains into interleaved lanes, with
  `ff::BatchInverter`-compatible constant-time zero handling. Batches under 32
  elements keep the single chain. Proof and verification timings are unchanged
  within noise; these inversions are a negligible share of a proof.
- Prepared the `1.0.0-rc.2` release.
- Updated the proving stack to `ff 0.14`, `group 0.14`, and `rand 0.10`.
- Forked from upstream `halo2_proofs` and renamed to `zakura-halo2-proofs`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.3.5); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
- Removed the unused `tempfile` dev-dependency inherited from upstream. Its
  `<3.7.0` cap held the workspace's `tempfile` at 3.6.0, whose `rustix 0.37`
  dependency no longer compiles on current Rust nightlies.
- The multi-opening prover and verifier now construct intermediate query sets
  in one pass.
- The multi-opening verifier now batch-inverts its Lagrange and vanishing
  denominators together, and rejects challenge collisions without panicking.
- Large single-worker Pasta multiscalar multiplications now use GLV scalar
  decomposition with signed-Booth buckets.
- The Pasta GLV Signed-Booth backend uses 10-bit windows for large
  single-worker multiscalar multiplications when its operation model favors
  them over 9-bit windows.
- Large multicore Pasta multiscalar multiplications now evaluate GLV
  signed-Booth windows in parallel when the backend cost model selects GLV.
- Large Pasta multiscalar multiplications batch affine bucket additions and
  invert their denominators in variable time. These multiscalar
  multiplications are already variable-time with respect to scalar digits and
  do not provide a constant-time guarantee.
- Batch verification now folds each proof's random batching scalar into its
  inner-product coefficient expansion.
- Common evaluation-domain rotations now bypass general exponentiation.
- Batch verification now reuses bounded per-parameter fixed-window tables when
  constructing instance commitments, with longer columns using the generic
  multiscalar multiplication path.
- Multi-opening proof construction now returns an invalid-input error instead
  of panicking when given no queries, and verification rejects empty query sets.
- Polynomial evaluation now shares missing-root products across complete
  compressed-selector families.
- Polynomial evaluation now combines compressed-selector contributions with a
  product tree, avoiding construction of every selector value separately, and
  adds unit-weighted terms without a field multiplication.
- Polynomial evaluation now caches repeated expressions whenever doing so
  avoids at least one field multiplication, and reuses cache buffers with
  disjoint lifetimes.
- Polynomial evaluation now consumes rotated polynomial chunks through
  borrowed slices when the surrounding operation can write its result directly.
- Polynomial evaluation now uses field squaring for structurally repeated
  multiplication operands.
- Polynomial evaluation now uses Horner's method for expanded fixed-base
  interpolation polynomials.
- Polynomial evaluation now shares repeated factors inside weighted constraint
  groups.
- Polynomial evaluation now caches repeated compiled subexpressions when doing
  so avoids at least three field multiplications.
- Polynomial evaluation now uses wide product accumulators when folding
  expressions over Pasta fields.
- Clarified internal vanishing-prover phase names to distinguish the random
  masking-polynomial commitment from quotient construction.
