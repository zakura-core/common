//! Fixed-length, position-weighted Sinsemilla evaluation.
//!
//! This moves the powers of two in the Sinsemilla recurrence into a
//! precomputed table:
//!
//! `B_i = [2^(N-i)] A_i`, so `B_(i+1) = B_i + [2^(N-i-1)] S[m_i]`.
//!
//! ## Exceptional-case reduction
//!
//! Let `A_0 = Q` and `A_(i+1) = [2] A_i + S[m_i]`. Before the first
//! exceptional incomplete addition, induction gives
//!
//! `A_i = [2^i] Q + sum_j [X_(i,j)] S[j]`,
//!
//! where `X_(i,j)` is the sum of `2^(i-1-t)` over the positions `t < i`
//! for which `m_t = j`.
//!
//! The first incomplete addition in a step can fail only when
//! `A_i = +/-S[m_i]`. If it succeeds, the second can fail only when
//! `A_i + S[m_i] = -A_i`; equality with `A_i` would imply
//! `S[m_i] = O`. Thus every exceptional step gives
//!
//! `[alpha] A_i + S[m_i] = O`
//!
//! for some `alpha` in `{-1, 1, 2}`. Substitution gives the efficiently
//! computable discrete-logarithm relation
//!
//! `[alpha * 2^i] Q
//!     + sum_j [alpha * X_(i,j) + delta_(j,m_i)] S[j] = O`.
//!
//! This relation is nontrivial because its coefficient of `Q` is nonzero.
//! In particular, `i < N` and `N <= C` (enforced using [`C`]) ensure that
//! its magnitude is at most `2^N <= 2^C <= (r_P - 1) / 2`, where `r_P` is
//! the Pallas group order.
//! Therefore an input on which this evaluator differs from [`HashDomain`]
//! yields a nontrivial discrete-logarithm relation among the independently
//! generated Sinsemilla bases. This is the reduction in the
//! [Sinsemilla exceptional-case theorem].
//!
//! Finding such a relation tightly reduces to the discrete logarithm
//! problem [by Jaeger and Tessaro]. The [Pasta curve parameters] give Pallas
//! a group order greater than `2^254`. Accounting conservatively for its
//! efficient order-3 endomorphism, the [Pollard-rho work estimate] is
//! `sqrt(pi * r_P / 12)`, which is greater than `2^126` classical group
//! operations. Triggering an omitted check is therefore considered infeasible
//! under the standard discrete-logarithm relation assumption.
//!
//! ## Required checks and invariants
//!
//! The reduction requires `Q` and every `S[j]` to be nonidentity, and it
//! requires `N <= C`. Construction checks these conditions. Evaluation also
//! checks the exact word count and that every word indexes the Sinsemilla
//! generator table. Callers must additionally use the table with the
//! [`HashDomain`] from which it was constructed; production domains must use
//! the protocol's independently personalized hash-to-curve generators.
//!
//! [Sinsemilla exceptional-case theorem]: https://zips.z.cash/protocol/protocol.pdf#thmsinsemillaex
//! [by Jaeger and Tessaro]: https://eprint.iacr.org/2020/1213.pdf#page=6
//! [Pasta curve parameters]: https://electriccoin.co/blog/the-pasta-curves-for-halo-2-and-beyond/
//! [Pollard-rho work estimate]: https://eprint.iacr.org/2019/1021.pdf#page=13

use alloc::{boxed::Box, vec::Vec};
use core::mem;

use group::{Curve, CurveAffine as _, Group};
use pasta_curves::{arithmetic::CurveAffine as _, pallas};

use super::{HashDomain, MessageWords, C, K, SINSEMILLA_S_AFFINE};

const GENERATOR_COUNT: usize = 1 << K;

/// Orchard levels for which the first two words have a combined table entry.
///
/// These are the widest levels in a batched 1024-leaf tree construction.
const FUSED_FIRST_WORDS: usize = 8;

/// Batches at least this large take the batch-affine evaluator in
/// [`UncheckedFixedLengthHashDomain::hash_words_batch`]; smaller ones keep
/// the projective paired evaluation, whose per-lane cost does not carry the
/// per-column shared field inversion.
///
/// Measured on the width-sweep bench: with portable field arithmetic the
/// affine path already wins at 16 lanes (−20% per hash on both Apple
/// aarch64 and x86-64), but with the `aarch64-asm` pasta backend the
/// multiplications it saves get cheaper while the per-column inversion does
/// not, and 16 lanes is a 9% *loss*; the crossover sits between 16 and 32,
/// and 32 wins on every configuration (−12% asm, −33% portable). The
/// threshold therefore sits at 32 so no build regresses; in a Merkle
/// rebuild the 16-lane level holds 16 of 1023 combines.
const BATCH_AFFINE_MIN_MESSAGES: usize = 32;

#[inline(always)]
fn square_with_runtime_backend(value: &pallas::Base) -> pallas::Base {
    // Method syntax selects `pallas::Base`'s portable inherent `const fn`.
    // Trait dispatch selects the configured runtime backend instead.
    group::ff::Field::square(value)
}

/// Two-lane Montgomery batch inversion for provably nonzero values (the
/// chord denominators of [`UncheckedFixedLengthHashDomain::evaluate_batch_affine`]).
///
/// Twin implementations — keep them in step when changing any:
/// `batch_invert_nonzero` in `pasta_curves/src/glv.rs` (the GLV ladder's
/// columns, same nonzero-only contract), `batch_invert_multi` in
/// `halo2_proofs/src/arithmetic.rs` (ff-style zero skipping), and
/// `Curve::batch_normalize` in `pasta_curves/src/curves.rs` (fused with the
/// Jacobian-to-affine conversion).
fn batch_invert_nonzero(values: &mut [pallas::Base], scratch: &mut [pallas::Base]) {
    use group::ff::Field;

    assert_eq!(values.len(), scratch.len());
    let mut acc0 = pallas::Base::one();
    let mut acc1 = pallas::Base::one();
    for (pair, slots) in values
        .as_chunks::<2>()
        .0
        .iter()
        .zip(scratch.as_chunks_mut::<2>().0)
    {
        debug_assert!(!pair[0].is_zero_vartime());
        debug_assert!(!pair[1].is_zero_vartime());
        slots[0] = acc0;
        acc0 *= pair[0];
        slots[1] = acc1;
        acc1 *= pair[1];
    }
    if let (Some(value), Some(slot)) = (
        values.as_chunks::<2>().1.first(),
        scratch.as_chunks_mut::<2>().1.first_mut(),
    ) {
        debug_assert!(!value.is_zero_vartime());
        *slot = acc0;
        acc0 *= value;
    }

    // A product of nonzero field elements is nonzero, so this cannot fail.
    let inverse = (acc0 * acc1).invert().unwrap();
    let seed0 = inverse * acc1;
    let seed1 = inverse * acc0;
    let mut acc0 = seed0;
    let mut acc1 = seed1;

    if let (Some(value), Some(slot)) = (
        values.as_chunks_mut::<2>().1.first_mut(),
        scratch.as_chunks::<2>().1.first(),
    ) {
        let inverted = acc0 * *slot;
        acc0 *= *value;
        *value = inverted;
    }
    for (pair, slots) in values
        .as_chunks_mut::<2>()
        .0
        .iter_mut()
        .zip(scratch.as_chunks::<2>().0)
        .rev()
    {
        let inverted0 = acc0 * slots[0];
        let inverted1 = acc1 * slots[1];
        acc0 *= pair[0];
        acc1 *= pair[1];
        pair[0] = inverted0;
        pair[1] = inverted1;
    }
}

fn extract(point: pallas::Point) -> pallas::Base {
    point
        .to_affine()
        .coordinates()
        .map(|coordinates| *coordinates.x())
        .unwrap_or_else(pallas::Base::zero)
}

/// An unchecked fixed-word-count Sinsemilla domain with position-weighted
/// generators.
///
/// Each instance is bound to the [`HashDomain`] it was constructed from;
/// instances built for different domains are interchangeable at the type
/// level, so callers must pair each table with messages for its own domain.
///
/// This evaluator deliberately omits Sinsemilla's incomplete-addition checks.
/// Finding an input that triggers one of those exceptional cases for the
/// protocol's independently generated `Q` and `S` points would exhibit a
/// nontrivial discrete-logarithm relation between those points, as shown in
/// the [module-level security argument](self). Callers that require exact
/// partial-function semantics must use [`HashDomain`] instead.
///
/// Construction is intentionally explicit and potentially expensive. Callers
/// should build this once and keep it outside timed or repeated hash paths.
pub struct UncheckedFixedLengthHashDomain<const N: usize> {
    /// Affine entries `W[e][j] = [2^e] S[j]` for `0 <= e < N - 1`,
    /// followed by the first-step accumulators
    /// `[2^N] Q + [2^(N-1)] S[j]`. Rows are flattened row-major.
    weighted_generators: Box<[pallas::Affine]>,
    /// Entries
    /// `[2^N] Q + [2^(N-1)] S[first] + [2^(N-2)] S[second]`, indexed by
    /// `first * GENERATOR_COUNT + second` for the first few `first` words.
    fused_first_two: Box<[pallas::Affine]>,
}

/// Reusable allocation storage for batched weighted hash evaluation.
///
/// The buffers remain separate allocations so the evaluator retains the
/// aliasing properties of its one-shot path. Retaining this value across
/// calls reuses their capacities.
#[derive(Debug, Default)]
pub struct BatchHashWorkspace {
    points: Vec<pallas::Point>,
    xs: Vec<pallas::Base>,
    ys: Vec<pallas::Base>,
    table_xs: Vec<pallas::Base>,
    table_ys: Vec<pallas::Base>,
    denominators: Vec<pallas::Base>,
    inversion_scratch: Vec<pallas::Base>,
}

impl<const N: usize> UncheckedFixedLengthHashDomain<N> {
    /// Precomputes the position-weighted table for `domain`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is zero, exceeds the protocol's maximum Sinsemilla word
    /// count, or the domain's `Q` is the identity.
    pub fn new(domain: &HashDomain) -> Self {
        assert!(N > 0, "the weighted evaluator requires at least one word");
        assert!(N <= C, "Sinsemilla word count exceeds the protocol limit");
        assert!(
            !bool::from(domain.Q.is_identity()),
            "the weighted evaluator requires a nonidentity Q"
        );

        let mut weighted_generators = Vec::with_capacity(N * GENERATOR_COUNT);

        let mut projective_row: Vec<_> = SINSEMILLA_S_AFFINE
            .iter()
            .copied()
            .map(pallas::Point::from)
            .collect();
        let mut affine_row: Vec<_> = SINSEMILLA_S_AFFINE.iter().copied().collect();

        for exponent in 0..N {
            assert!(affine_row
                .iter()
                .all(|point| !bool::from(point.is_identity())));
            weighted_generators.extend(affine_row.iter().copied());

            if exponent + 1 < N {
                projective_row
                    .iter_mut()
                    .for_each(|point| *point = point.double());
                pallas::Point::batch_normalize(&projective_row, &mut affine_row);
            }
        }

        assert_eq!(weighted_generators.len(), N * GENERATOR_COUNT);

        let initial = (0..N).fold(domain.Q, |point, _| point.double());
        let first_row_start = (N - 1) * GENERATOR_COUNT;
        let first_accumulator_points: Vec<_> = weighted_generators[first_row_start..]
            .iter()
            .map(|generator| initial + generator)
            .collect();
        pallas::Point::batch_normalize(
            &first_accumulator_points,
            &mut weighted_generators[first_row_start..],
        );
        assert!(weighted_generators[first_row_start..]
            .iter()
            .all(|point| !bool::from(point.is_identity())));

        let mut fused_first_two = Vec::new();
        if N > 1 {
            fused_first_two.reserve(FUSED_FIRST_WORDS * GENERATOR_COUNT);
            let second_row_start = (N - 2) * GENERATOR_COUNT;
            let second_generators =
                weighted_generators[second_row_start..second_row_start + GENERATOR_COUNT].to_vec();
            let mut normalized = second_generators.clone();

            for first in 0..FUSED_FIRST_WORDS {
                let first_accumulator =
                    pallas::Point::from(weighted_generators[first_row_start + first]);
                let points: Vec<_> = second_generators
                    .iter()
                    .map(|second| first_accumulator + second)
                    .collect();
                pallas::Point::batch_normalize(&points, &mut normalized);
                fused_first_two.extend(normalized.iter().copied());
            }
        }

        Self {
            weighted_generators: weighted_generators.into_boxed_slice(),
            fused_first_two: fused_first_two.into_boxed_slice(),
        }
    }

    /// Evaluates exactly `N` pre-decoded Sinsemilla words to a point.
    ///
    /// # Panics
    ///
    /// Panics if any word is not a valid [`K`]-bit Sinsemilla word.
    pub fn hash_words_to_point(&self, words: &[u16; N]) -> pallas::Point {
        self.evaluate(words.iter().copied())
    }

    /// Evaluates the Sinsemilla hash of exactly `N` pre-decoded words.
    ///
    /// # Panics
    ///
    /// Panics if any word is not a valid [`K`]-bit Sinsemilla word.
    pub fn hash_words(&self, words: &[u16; N]) -> pallas::Base {
        extract(self.hash_words_to_point(words))
    }

    /// Evaluates a batch of `N`-word messages position-first and returns their
    /// extracted Sinsemilla hashes.
    ///
    /// The projective results are normalized together, sharing a single field
    /// inversion across the batch. An empty batch returns an empty [`Vec`].
    ///
    /// # Panics
    ///
    /// Panics if any word is not a valid [`K`]-bit Sinsemilla word.
    pub fn hash_words_batch(&self, messages: &[[u16; N]]) -> Vec<pallas::Base> {
        let mut workspace = BatchHashWorkspace::default();
        self.hash_words_batch_with_workspace(messages, &mut workspace);
        workspace.xs
    }

    /// Evaluates a batch while retaining temporary allocations in
    /// `workspace`, and returns the extracted hashes stored there.
    ///
    /// The returned slice remains valid until `workspace` is mutably borrowed
    /// again. An empty batch returns an empty slice.
    ///
    /// # Panics
    ///
    /// Panics if any word is not a valid [`K`]-bit Sinsemilla word.
    pub fn hash_words_batch_with_workspace<'a>(
        &self,
        messages: &[[u16; N]],
        workspace: &'a mut BatchHashWorkspace,
    ) -> &'a [pallas::Base] {
        use group::ff::Field;
        use pasta_curves::arithmetic::CurveExt;

        if messages.len() >= BATCH_AFFINE_MIN_MESSAGES {
            self.evaluate_batch_affine(messages, workspace);
            return &workspace.xs;
        }

        self.evaluate_batch(messages, &mut workspace.points);

        // Fused batch x-extraction, sharing one field inversion across the
        // batch. A full `batch_normalize` would also compute every
        // y-coordinate (`1/z^3` and a further multiplication per point) into
        // an intermediate affine buffer, only for extraction to discard
        // them; here the backward pass writes `x / z^2` straight into the
        // result vector. That vector also doubles as the prefix-product
        // store for Montgomery's trick during the forward pass (the
        // backward step needs each point's `z` and the prefix before it),
        // so no scratch allocation is needed. An identity result — only
        // reachable through the infeasible exceptional cases (see the
        // module docs) — extracts to zero, matching [`extract`], and an
        // empty batch runs zero iterations around an inversion of one.
        workspace
            .xs
            .resize(workspace.points.len(), pallas::Base::zero());
        let mut acc = pallas::Base::one();
        for (point, slot) in workspace.points.iter().zip(workspace.xs.iter_mut()) {
            let (_, _, z) = point.jacobian_coordinates();
            *slot = acc;
            if !z.is_zero_vartime() {
                acc *= z;
            }
        }
        // Skipped (identity) points never enter the product.
        let mut acc = acc.invert().unwrap();
        for (point, slot) in workspace.points.iter().zip(workspace.xs.iter_mut()).rev() {
            let (x, _, z) = point.jacobian_coordinates();
            if z.is_zero_vartime() {
                *slot = pallas::Base::zero();
            } else {
                let z_inv = acc * *slot;
                acc *= z;
                *slot = x * square_with_runtime_backend(&z_inv);
            }
        }
        &workspace.xs
    }

    /// Evaluates a batch on **affine** accumulators: every lane performs its
    /// position-`i` addition in lockstep (the schedule is fixed by `N`, not
    /// by the messages), so each column batch-inverts its chord denominators
    /// across the batch with one shared field inversion, and each addition
    /// is the plain affine chord formula (2M + 1S after the inversion) in
    /// place of a projective mixed addition. The accumulators finish in
    /// affine form, so the returned hashes are simply their x-coordinates —
    /// no normalization pass at all.
    ///
    /// The chord formula is undefined when a lane's accumulator collides
    /// with its table point (`x` equal: the lane is adding `±P` to `P`) or
    /// is the identity; both are exactly the exceptional cases of the
    /// module-level discrete-logarithm reduction, so — as with the omitted
    /// mixed-addition checks — they are infeasible to reach and are not
    /// checked. The denominators are therefore provably nonzero, which the
    /// lean batched inversion below relies on.
    ///
    /// Both the inversion and the field arithmetic run two interleaved
    /// even/odd lanes so the dependency chains overlap (the same
    /// construction as the two-lane batched inversions elsewhere in the
    /// workspace).
    fn evaluate_batch_affine(&self, messages: &[[u16; N]], workspace: &mut BatchHashWorkspace) {
        let n = messages.len();
        let BatchHashWorkspace {
            xs,
            ys,
            table_xs,
            table_ys,
            denominators,
            inversion_scratch,
            ..
        } = workspace;
        xs.clear();
        ys.clear();
        xs.reserve(n);
        ys.reserve(n);
        let first_word = messages[0][0];
        let first_generator = usize::from(first_word);
        assert!(first_generator < GENERATOR_COUNT, "invalid Sinsemilla word");
        let shared_first = messages[1..].iter().all(|message| message[0] == first_word);
        let start = if N > 1 && shared_first && first_generator < FUSED_FIRST_WORDS {
            for message in messages {
                let second_generator = usize::from(message[1]);
                assert!(
                    second_generator < GENERATOR_COUNT,
                    "invalid Sinsemilla word"
                );
                let (x, y) = self
                    .fused_first_two(first_generator, second_generator)
                    .raw_coordinates();
                xs.push(x);
                ys.push(y);
            }
            2
        } else if shared_first {
            let (x, y) = self.first_accumulator(first_generator).raw_coordinates();
            xs.resize(n, x);
            ys.resize(n, y);
            1
        } else {
            for message in messages {
                let generator = usize::from(message[0]);
                assert!(generator < GENERATOR_COUNT, "invalid Sinsemilla word");
                let (x, y) = self.first_accumulator(generator).raw_coordinates();
                xs.push(x);
                ys.push(y);
            }
            1
        };
        table_xs.resize(n, pallas::Base::zero());
        table_ys.resize(n, pallas::Base::zero());
        denominators.resize(n, pallas::Base::zero());
        inversion_scratch.resize(n, pallas::Base::zero());

        // The precomputed first accumulators above replace the `i = 0`
        // column, including its shared inversion and per-lane chord work.
        for i in start..N {
            let exponent = N - i - 1;
            for (lane, message) in messages.iter().enumerate() {
                let generator = usize::from(message[i]);
                assert!(generator < GENERATOR_COUNT, "invalid Sinsemilla word");
                // Construction proves every table entry nonidentity, so the
                // raw pair avoids repeating that check for each batch lane.
                let (table_x, table_y) = self
                    .weighted_generator(exponent, generator)
                    .raw_coordinates();
                table_xs[lane] = table_x;
                table_ys[lane] = table_y;
                denominators[lane] = table_xs[lane] - xs[lane];
            }

            batch_invert_nonzero(denominators, inversion_scratch);

            // Affine chord additions, two lanes interleaved.
            let pairs = n / 2;
            for pair in 0..pairs {
                let (a, b) = (2 * pair, 2 * pair + 1);
                let lambda_a = (table_ys[a] - ys[a]) * denominators[a];
                let lambda_b = (table_ys[b] - ys[b]) * denominators[b];
                let x3_a = square_with_runtime_backend(&lambda_a) - xs[a] - table_xs[a];
                let x3_b = square_with_runtime_backend(&lambda_b) - xs[b] - table_xs[b];
                ys[a] = lambda_a * (xs[a] - x3_a) - ys[a];
                ys[b] = lambda_b * (xs[b] - x3_b) - ys[b];
                xs[a] = x3_a;
                xs[b] = x3_b;
            }
            if n % 2 == 1 {
                let a = n - 1;
                let lambda = (table_ys[a] - ys[a]) * denominators[a];
                let x3 = square_with_runtime_backend(&lambda) - xs[a] - table_xs[a];
                ys[a] = lambda * (xs[a] - x3) - ys[a];
                xs[a] = x3;
            }
        }
    }

    fn evaluate_batch(&self, messages: &[[u16; N]], points: &mut Vec<pallas::Point>) {
        points.clear();
        points.reserve(messages.len());
        let mut start = 1;
        if let Some(first_message) = messages.first() {
            let first_word = first_message[0];
            let first_generator = usize::from(first_word);
            assert!(first_generator < GENERATOR_COUNT, "invalid Sinsemilla word");
            let shared_first = messages[1..].iter().all(|message| message[0] == first_word);
            if N > 1 && shared_first && first_generator < FUSED_FIRST_WORDS {
                for message in messages {
                    let second_generator = usize::from(message[1]);
                    assert!(
                        second_generator < GENERATOR_COUNT,
                        "invalid Sinsemilla word"
                    );
                    points.push(
                        self.fused_first_two(first_generator, second_generator)
                            .into(),
                    );
                }
                start = 2;
            } else if shared_first {
                points.resize(
                    messages.len(),
                    self.first_accumulator(first_generator).into(),
                );
            } else {
                for message in messages {
                    let generator = usize::from(message[0]);
                    assert!(generator < GENERATOR_COUNT, "invalid Sinsemilla word");
                    points.push(self.first_accumulator(generator).into());
                }
            }
        }

        // The precomputed first accumulators above replace the `i = 0`
        // column and its mixed addition.
        for i in start..N {
            let exponent = N - i - 1;
            let mut point_pairs = points.chunks_exact_mut(2);
            let mut message_pairs = messages.chunks_exact(2);

            for (point_pair, message_pair) in point_pairs.by_ref().zip(&mut message_pairs) {
                let generator_0 = usize::from(message_pair[0][i]);
                let generator_1 = usize::from(message_pair[1][i]);
                assert!(generator_0 < GENERATOR_COUNT, "invalid Sinsemilla word");
                assert!(generator_1 < GENERATOR_COUNT, "invalid Sinsemilla word");

                // The module-level discrete-logarithm reduction establishes
                // that these weighted additions cannot feasibly encounter an
                // exceptional input.
                let sum = pallas::add_mixed_pair_unchecked(
                    &point_pair[0],
                    &self.weighted_generator(exponent, generator_0),
                    &point_pair[1],
                    &self.weighted_generator(exponent, generator_1),
                );
                point_pair.copy_from_slice(&sum);
            }

            if let (Some(point), Some(words)) = (
                point_pairs.into_remainder().first_mut(),
                message_pairs.remainder().first(),
            ) {
                let generator = usize::from(words[i]);
                assert!(generator < GENERATOR_COUNT, "invalid Sinsemilla word");
                *point += self.weighted_generator(exponent, generator);
            }
        }
    }

    /// Evaluates a bit iterator whose padded representation is exactly `N`
    /// Sinsemilla words.
    ///
    /// # Panics
    ///
    /// Panics if the zero-padded message is not exactly `N` words long.
    pub fn hash_to_point(&self, msg: impl Iterator<Item = bool>) -> pallas::Point {
        self.evaluate(
            MessageWords::new(msg)
                .map(|word| u16::try_from(word).expect("a Sinsemilla word fits into u16")),
        )
    }

    /// Evaluates the Sinsemilla hash of a bit iterator whose padded
    /// representation is exactly `N` words.
    ///
    /// # Panics
    ///
    /// Panics as [`Self::hash_to_point`] does.
    pub fn hash(&self, msg: impl Iterator<Item = bool>) -> pallas::Base {
        extract(self.hash_to_point(msg))
    }

    /// Returns the heap size occupied by the weighted generator table.
    pub fn table_bytes(&self) -> usize {
        (self.weighted_generators.len() + self.fused_first_two.len())
            * mem::size_of::<pallas::Affine>()
    }

    fn evaluate(&self, words: impl Iterator<Item = u16>) -> pallas::Point {
        let mut words = words;
        let first_word = words.next().expect("unexpected Sinsemilla word count");
        let first_generator = usize::from(first_word);
        assert!(first_generator < GENERATOR_COUNT, "invalid Sinsemilla word");
        let mut start = 1;
        let mut point = if N > 1 && first_generator < FUSED_FIRST_WORDS {
            let second_word = words.next().expect("unexpected Sinsemilla word count");
            let second_generator = usize::from(second_word);
            assert!(
                second_generator < GENERATOR_COUNT,
                "invalid Sinsemilla word"
            );
            start = 2;
            self.fused_first_two(first_generator, second_generator)
                .into()
        } else {
            self.first_accumulator(first_generator).into()
        };

        for i in start..N {
            let word = words.next().expect("unexpected Sinsemilla word count");
            let generator_index = usize::from(word);
            assert!(generator_index < GENERATOR_COUNT, "invalid Sinsemilla word");

            let exponent = N - i - 1;
            point += self.weighted_generator(exponent, generator_index);
        }
        assert!(words.next().is_none(), "unexpected Sinsemilla word count");
        point
    }

    fn weighted_generator(&self, exponent: usize, generator: usize) -> pallas::Affine {
        debug_assert!(exponent + 1 < N);
        self.weighted_generators[exponent * GENERATOR_COUNT + generator]
    }

    fn first_accumulator(&self, generator: usize) -> pallas::Affine {
        self.weighted_generators[(N - 1) * GENERATOR_COUNT + generator]
    }

    fn fused_first_two(&self, first: usize, second: usize) -> pallas::Affine {
        debug_assert!(N > 1);
        debug_assert!(first < FUSED_FIRST_WORDS);
        self.fused_first_two[first * GENERATOR_COUNT + second]
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use group::{Curve, CurveAffine as _, Group};
    use pasta_curves::pallas;
    use subtle::CtOption;

    use super::{UncheckedFixedLengthHashDomain, GENERATOR_COUNT};
    use crate::{HashDomain, K, SINSEMILLA_S_AFFINE};

    const MERKLE_WORDS: usize = 52;
    const MERKLE_DOMAIN: &str = "z.cash:Orchard-MerkleCRH";

    fn assert_matches(expected: CtOption<pallas::Point>, actual: pallas::Point) {
        assert!(bool::from(expected.is_some()));
        assert_eq!(actual, expected.unwrap());
    }

    fn words_to_bits(words: &[u16]) -> Vec<bool> {
        words
            .iter()
            .flat_map(|word| (0..K).map(move |bit| ((word >> bit) & 1) == 1))
            .collect()
    }

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut value = *state;
        value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        value ^ (value >> 31)
    }

    #[test]
    fn unchecked_evaluator_deliberately_skips_incomplete_addition_failure() {
        let generator_index = 0;
        let generator = SINSEMILLA_S_AFFINE[generator_index];
        let generator_point = pallas::Point::from(generator);
        let domain = HashDomain::from_Q(generator_point);
        let unchecked = UncheckedFixedLengthHashDomain::<1>::new(&domain);
        let words = [generator_index as u16];
        let bits = words_to_bits(&words);

        // The first incomplete addition attempts S + S, so the specified
        // partial function returns bottom. The unchecked evaluator computes
        // the corresponding complete group expression instead.
        assert!(!bool::from(
            domain.hash_to_point(bits.iter().copied()).is_some()
        ));
        assert_eq!(
            unchecked.hash_words_to_point(&words),
            generator_point.double() + generator
        );
    }

    #[test]
    #[should_panic(expected = "the weighted evaluator requires a nonidentity Q")]
    fn rejects_identity_q() {
        let domain = HashDomain::from_Q(pallas::Point::identity());
        let _ = UncheckedFixedLengthHashDomain::<1>::new(&domain);
    }

    #[test]
    fn fixed_merkle_length_matches_generic_evaluation() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = UncheckedFixedLengthHashDomain::<MERKLE_WORDS>::new(&domain);

        let mut fixtures = vec![
            [0; MERKLE_WORDS],
            [1; MERKLE_WORDS],
            [(GENERATOR_COUNT - 1) as u16; MERKLE_WORDS],
        ];
        fixtures.push(core::array::from_fn(|i| i as u16));

        let mut state = 0x5369_6e73_656d_696c;
        fixtures.extend((0..128).map(|_| {
            core::array::from_fn(|_| (splitmix64(&mut state) as usize % GENERATOR_COUNT) as u16)
        }));

        for words in fixtures {
            let bits = words_to_bits(&words);
            let expected = domain.hash_to_point(bits.iter().copied());
            assert_matches(expected, weighted.hash_words_to_point(&words));
            assert_matches(expected, weighted.hash_to_point(bits.iter().copied()));

            let expected = domain.hash(bits.iter().copied());
            assert!(bool::from(expected.is_some()));
            let expected = expected.unwrap();
            assert_eq!(expected, weighted.hash_words(&words));
            assert_eq!(expected, weighted.hash(bits.iter().copied()));
        }
    }

    #[test]
    fn batch_matches_individual_word_evaluation() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = UncheckedFixedLengthHashDomain::<MERKLE_WORDS>::new(&domain);
        let mut workspace = super::BatchHashWorkspace::default();
        let mut state = 0x5369_6e73_656d_696c;
        let messages: Vec<_> = (0..64)
            .map(|_| {
                core::array::from_fn(|_| (splitmix64(&mut state) as usize % GENERATOR_COUNT) as u16)
            })
            .collect();
        let expected: Vec<_> = messages
            .iter()
            .map(|words| weighted.hash_words(words))
            .collect();

        // Cover the projective fallback, both sides of the batch-affine
        // threshold, and odd batch widths on both paths.
        for width in [
            1,
            2,
            3,
            super::BATCH_AFFINE_MIN_MESSAGES - 1,
            super::BATCH_AFFINE_MIN_MESSAGES,
            17,
            33,
            64,
        ] {
            assert_eq!(
                weighted.hash_words_batch(&messages[..width]),
                expected[..width],
                "width {}",
                width
            );
            assert_eq!(
                weighted.hash_words_batch_with_workspace(&messages[..width], &mut workspace,),
                &expected[..width],
                "workspace width {}",
                width
            );
        }
        assert!(weighted.hash_words_batch(&[]).is_empty());
        assert!(weighted
            .hash_words_batch_with_workspace(&[], &mut workspace)
            .is_empty());
    }

    #[test]
    #[should_panic(expected = "invalid Sinsemilla word")]
    fn batch_rejects_invalid_words() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = UncheckedFixedLengthHashDomain::<1>::new(&domain);
        weighted.hash_words_batch(&[[GENERATOR_COUNT as u16]]);
    }

    #[test]
    #[should_panic(expected = "unexpected Sinsemilla word count")]
    fn rejects_too_few_message_words() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = UncheckedFixedLengthHashDomain::<2>::new(&domain);
        weighted.hash_to_point(core::iter::repeat_n(false, K));
    }

    #[test]
    #[should_panic(expected = "unexpected Sinsemilla word count")]
    fn rejects_too_many_message_words() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = UncheckedFixedLengthHashDomain::<2>::new(&domain);
        weighted.hash_to_point(core::iter::repeat_n(false, 3 * K));
    }

    #[test]
    fn weighted_table_is_a_doubling_chain() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = UncheckedFixedLengthHashDomain::<MERKLE_WORDS>::new(&domain);
        let initial = (0..MERKLE_WORDS).fold(domain.Q, |point, _| point.double());

        assert_eq!(
            weighted.table_bytes(),
            (MERKLE_WORDS + super::FUSED_FIRST_WORDS)
                * GENERATOR_COUNT
                * core::mem::size_of::<pallas::Affine>()
        );

        for generator in 0..GENERATOR_COUNT {
            assert_eq!(
                weighted.weighted_generator(0, generator),
                SINSEMILLA_S_AFFINE[generator]
            );
            for exponent in 0..MERKLE_WORDS - 1 {
                let entry = weighted.weighted_generator(exponent, generator);
                assert!(!bool::from(entry.is_identity()));
                let doubled = pallas::Point::from(entry).double().to_affine();

                // Adjacent rows chain by doubling.
                if exponent + 1 < MERKLE_WORDS - 1 {
                    assert_eq!(
                        weighted.weighted_generator(exponent + 1, generator),
                        doubled
                    );
                }
            }

            let first_generator =
                pallas::Point::from(weighted.weighted_generator(MERKLE_WORDS - 2, generator))
                    .double();
            assert_eq!(
                weighted.first_accumulator(generator),
                (initial + first_generator).to_affine()
            );
        }
    }
}
