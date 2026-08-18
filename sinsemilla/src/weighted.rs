//! Fixed-length, position-weighted Sinsemilla evaluation.
//!
//! This moves the powers of two in the Sinsemilla recurrence into a
//! precomputed table:
//!
//! `B_i = [2^(N-i)] A_i`, so `B_(i+1) = B_i + [2^(N-i-1)] S[m_i]`.

use alloc::{boxed::Box, vec, vec::Vec};
use core::mem;

use group::{prime::PrimeCurveAffine, Curve, Group};
use pasta_curves::{
    arithmetic::{CurveAffine, CurveExt},
    pallas,
};
use subtle::{ConstantTimeEq, CtOption};

use super::{lebs2ip_k, HashDomain, Pad, C, K, SINSEMILLA_S_AFFINE};

const GENERATOR_COUNT: usize = 1 << K;

/// One weighted generator `W[e][j]` paired with the affine x-coordinate of
/// its double `W[e+1][j]`, so each step reads one contiguous table entry.
#[derive(Clone, Copy)]
struct WeightedGenerator {
    point: pallas::Affine,
    doubled_x: pallas::Base,
}

/// A fixed-word-count Sinsemilla domain with position-weighted generators.
///
/// Each instance is bound to the [`HashDomain`] it was constructed from;
/// instances built for different domains are interchangeable at the type
/// level, so callers must pair each table with messages for its own domain.
///
/// Construction is intentionally explicit and potentially expensive. Callers
/// should build this once and keep it outside timed or repeated hash paths.
pub struct FixedLengthHashDomain<const N: usize> {
    initial: pallas::Point,
    /// Interleaved entries `(W[e][j], x(W[e+1][j]))` with `W[e][j] = [2^e]
    /// S[j]`, flattened row-major for `0 <= e < N` and `0 <= j < 2^K`.
    weighted_generators: Box<[WeightedGenerator]>,
}

impl<const N: usize> FixedLengthHashDomain<N> {
    /// Precomputes the position-weighted table for `domain`.
    ///
    /// # Panics
    ///
    /// Panics if `N` is zero or exceeds the protocol's maximum Sinsemilla
    /// word count.
    pub fn new(domain: &HashDomain) -> Self {
        assert!(N > 0, "the weighted evaluator requires at least one word");
        assert!(N <= C, "Sinsemilla word count exceeds the protocol limit");

        let mut weighted_generators = Vec::with_capacity(N * GENERATOR_COUNT);

        let mut projective_row: Vec<_> = SINSEMILLA_S_AFFINE
            .iter()
            .copied()
            .map(pallas::Point::from)
            .collect();
        let mut current_row: Vec<_> = SINSEMILLA_S_AFFINE.iter().copied().collect();
        let mut doubled_row = vec![pallas::Affine::identity(); GENERATOR_COUNT];

        for _ in 0..N {
            projective_row
                .iter_mut()
                .for_each(|point| *point = point.double());
            pallas::Point::batch_normalize(&projective_row, &mut doubled_row);
            assert!(doubled_row
                .iter()
                .all(|point| !bool::from(point.is_identity())));
            weighted_generators.extend(current_row.iter().zip(&doubled_row).map(
                |(generator, doubled)| WeightedGenerator {
                    point: *generator,
                    // The assertion above guarantees affine coordinates exist.
                    doubled_x: *doubled.coordinates().unwrap().x(),
                },
            ));
            mem::swap(&mut current_row, &mut doubled_row);
        }

        assert_eq!(weighted_generators.len(), N * GENERATOR_COUNT);

        let initial = (0..N).fold(domain.Q, |point, _| point.double());

        Self {
            initial,
            weighted_generators: weighted_generators.into_boxed_slice(),
        }
    }

    /// Evaluates exactly `N` pre-decoded Sinsemilla words.
    ///
    /// # Panics
    ///
    /// Panics if any word is not a valid `K`-bit Sinsemilla word.
    pub fn hash_words(&self, words: &[u16; N]) -> CtOption<pallas::Point> {
        self.evaluate(words.iter().copied())
    }

    /// Evaluates a bit iterator whose padded representation is exactly `N`
    /// Sinsemilla words.
    ///
    /// # Panics
    ///
    /// Panics if the zero-padded message is not exactly `N` words long.
    pub fn hash_to_point(&self, msg: impl Iterator<Item = bool>) -> CtOption<pallas::Point> {
        let padded: Vec<_> = Pad::new(msg).collect();
        assert_eq!(padded.len(), N * K, "unexpected padded message length");

        self.evaluate(padded.chunks_exact(K).map(|chunk| {
            u16::try_from(lebs2ip_k(chunk.try_into().expect("correct length")))
                .expect("a Sinsemilla word fits into u16")
        }))
    }

    /// Evaluates the Sinsemilla hash of a bit iterator whose padded
    /// representation is exactly `N` words.
    ///
    /// # Panics
    ///
    /// Panics as [`Self::hash_to_point`] does.
    pub fn hash(&self, msg: impl Iterator<Item = bool>) -> CtOption<pallas::Base> {
        super::extract_p_bottom(self.hash_to_point(msg))
    }

    /// Returns the heap size occupied by the weighted generator table.
    pub fn table_bytes(&self) -> usize {
        self.weighted_generators.len() * mem::size_of::<WeightedGenerator>()
    }

    fn evaluate(&self, words: impl ExactSizeIterator<Item = u16>) -> CtOption<pallas::Point> {
        assert_eq!(words.len(), N, "unexpected Sinsemilla word count");

        words
            .enumerate()
            .fold(CtOption::new(self.initial, 1.into()), |acc, (i, word)| {
                let generator_index = usize::from(word);
                assert!(generator_index < GENERATOR_COUNT, "invalid Sinsemilla word");

                let exponent = N - i - 1;
                let entry = self.weighted_generator(exponent, generator_index);

                weighted_step(acc, entry.point, entry.doubled_x)
            })
    }

    fn weighted_generator(&self, exponent: usize, generator: usize) -> WeightedGenerator {
        self.weighted_generators[exponent * GENERATOR_COUNT + generator]
    }
}

/// Applies one scaled transition while preserving the canonical incomplete-
/// addition failure conditions.
fn weighted_step(
    acc: CtOption<pallas::Point>,
    generator: pallas::Affine,
    doubled_generator_x: pallas::Base,
) -> CtOption<pallas::Point> {
    acc.and_then(|point| {
        let (point_x, _, point_z) = point.jacobian_coordinates();

        // In scaled coordinates, A = +/-S iff B = +/-[2]G. The two signs
        // have the same affine x-coordinate.
        let same_x = point_x.ct_eq(&(doubled_generator_x * point_z.square()));
        let next = point + generator;

        CtOption::new(next, !(point.is_identity() | same_x | next.is_identity()))
    })
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use group::{ff::PrimeField, prime::PrimeCurveAffine, Curve, Group};
    use pasta_curves::{arithmetic::CurveAffine, pallas};
    use subtle::CtOption;

    use super::{weighted_step, FixedLengthHashDomain, WeightedGenerator, GENERATOR_COUNT};
    use crate::{HashDomain, IncompletePoint, K, SINSEMILLA_S_AFFINE};

    const MERKLE_WORDS: usize = 52;
    const MERKLE_DOMAIN: &str = "z.cash:Orchard-MerkleCRH";

    fn assert_same(expected: CtOption<pallas::Point>, actual: CtOption<pallas::Point>) {
        let expected_is_some = bool::from(expected.is_some());
        assert_eq!(bool::from(actual.is_some()), expected_is_some);
        if expected_is_some {
            assert_eq!(actual.unwrap(), expected.unwrap());
        }
    }

    fn canonical_step(point: pallas::Point, generator: pallas::Affine) -> CtOption<pallas::Point> {
        let point = IncompletePoint::from(point);
        ((point + generator) + point).into()
    }

    fn affine_x(point: pallas::Affine) -> pallas::Base {
        *point.coordinates().unwrap().x()
    }

    fn scaled_step(point: pallas::Point, generator: pallas::Affine) -> CtOption<pallas::Point> {
        let doubled_x = affine_x(pallas::Point::from(generator).double().to_affine());
        weighted_step(
            CtOption::new(point.double(), 1.into()),
            generator,
            doubled_x,
        )
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
    fn weighted_step_preserves_every_generator_exception() {
        let generator = pallas::Point::generator();

        for (index, s) in SINSEMILLA_S_AFFINE.iter().copied().enumerate() {
            assert!(!bool::from(s.is_identity()), "identity generator {index}");
            let s_point = pallas::Point::from(s);

            for point in [
                pallas::Point::identity(),
                s_point,
                -s_point,
                -(s_point * pallas::Scalar::TWO_INV),
                s_point * pallas::Scalar::TWO_INV,
                generator * pallas::Scalar::from(index as u64 + 1),
            ] {
                assert_same(canonical_step(point, s), scaled_step(point, s));
            }
        }
    }

    #[test]
    fn fixed_merkle_length_matches_generic_evaluation() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = FixedLengthHashDomain::<MERKLE_WORDS>::new(&domain);

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
            assert_same(expected, weighted.hash_words(&words));
            assert_same(expected, weighted.hash_to_point(bits.iter().copied()));
        }
    }

    #[test]
    fn weighted_table_is_a_doubling_chain() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = FixedLengthHashDomain::<MERKLE_WORDS>::new(&domain);

        assert_eq!(
            weighted.table_bytes(),
            MERKLE_WORDS * GENERATOR_COUNT * core::mem::size_of::<WeightedGenerator>()
        );

        for generator in 0..GENERATOR_COUNT {
            assert_eq!(
                weighted.weighted_generator(0, generator).point,
                SINSEMILLA_S_AFFINE[generator]
            );
            for exponent in 0..MERKLE_WORDS {
                let entry = weighted.weighted_generator(exponent, generator);
                let doubled = pallas::Point::from(entry.point).double().to_affine();

                // Each entry pairs a generator with its double's x-coordinate.
                assert_eq!(entry.doubled_x, affine_x(doubled));

                // Adjacent rows chain by doubling.
                if exponent + 1 < MERKLE_WORDS {
                    assert_eq!(
                        weighted.weighted_generator(exponent + 1, generator).point,
                        doubled
                    );
                }
            }
        }
    }
}
