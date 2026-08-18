//! Fixed-length, position-weighted Sinsemilla evaluation.
//!
//! This moves the powers of two in the Sinsemilla recurrence into a
//! precomputed table:
//!
//! `B_i = [2^(N-i)] A_i`, so `B_(i+1) = B_i + [2^(N-i-1)] S[m_i]`.

use alloc::{boxed::Box, vec::Vec};
use core::mem;

use group::{prime::PrimeCurveAffine, Curve, Group};
use pasta_curves::{arithmetic::CurveAffine, pallas};

use super::{lebs2ip_k, HashDomain, Pad, C, K, SINSEMILLA_S_AFFINE};

const GENERATOR_COUNT: usize = 1 << K;

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
/// nontrivial multi-base discrete-log relation between those points. Callers
/// that require exact partial-function semantics must use [`HashDomain`]
/// instead.
///
/// Construction is intentionally explicit and potentially expensive. Callers
/// should build this once and keep it outside timed or repeated hash paths.
pub struct UncheckedFixedLengthHashDomain<const N: usize> {
    initial: pallas::Point,
    /// Affine entries `W[e][j] = [2^e] S[j]`, flattened row-major for
    /// `0 <= e < N` and `0 <= j < 2^K`.
    weighted_generators: Box<[pallas::Affine]>,
}

impl<const N: usize> UncheckedFixedLengthHashDomain<N> {
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
    pub fn hash_words(&self, words: &[u16; N]) -> pallas::Point {
        self.evaluate(words.iter().copied())
    }

    /// Evaluates a bit iterator whose padded representation is exactly `N`
    /// Sinsemilla words.
    ///
    /// # Panics
    ///
    /// Panics if the zero-padded message is not exactly `N` words long.
    pub fn hash_to_point(&self, msg: impl Iterator<Item = bool>) -> pallas::Point {
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
    pub fn hash(&self, msg: impl Iterator<Item = bool>) -> pallas::Base {
        self.hash_to_point(msg)
            .to_affine()
            .coordinates()
            .map(|coordinates| *coordinates.x())
            .unwrap_or_else(pallas::Base::zero)
    }

    /// Returns the heap size occupied by the weighted generator table.
    pub fn table_bytes(&self) -> usize {
        self.weighted_generators.len() * mem::size_of::<pallas::Affine>()
    }

    fn evaluate(&self, words: impl ExactSizeIterator<Item = u16>) -> pallas::Point {
        assert_eq!(words.len(), N, "unexpected Sinsemilla word count");

        words.enumerate().fold(self.initial, |point, (i, word)| {
            let generator_index = usize::from(word);
            assert!(generator_index < GENERATOR_COUNT, "invalid Sinsemilla word");

            let exponent = N - i - 1;
            point + self.weighted_generator(exponent, generator_index)
        })
    }

    fn weighted_generator(&self, exponent: usize, generator: usize) -> pallas::Affine {
        self.weighted_generators[exponent * GENERATOR_COUNT + generator]
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use group::{prime::PrimeCurveAffine, Curve, Group};
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
            unchecked.hash_words(&words),
            generator_point.double() + generator
        );
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
            assert_matches(expected, weighted.hash_words(&words));
            assert_matches(expected, weighted.hash_to_point(bits.iter().copied()));

            let expected = domain.hash(bits.iter().copied());
            assert!(bool::from(expected.is_some()));
            assert_eq!(expected.unwrap(), weighted.hash(bits.iter().copied()));
        }
    }

    #[test]
    fn weighted_table_is_a_doubling_chain() {
        let domain = HashDomain::new(MERKLE_DOMAIN);
        let weighted = UncheckedFixedLengthHashDomain::<MERKLE_WORDS>::new(&domain);

        assert_eq!(
            weighted.table_bytes(),
            MERKLE_WORDS * GENERATOR_COUNT * core::mem::size_of::<pallas::Affine>()
        );

        for generator in 0..GENERATOR_COUNT {
            assert_eq!(
                weighted.weighted_generator(0, generator),
                SINSEMILLA_S_AFFINE[generator]
            );
            for exponent in 0..MERKLE_WORDS {
                let entry = weighted.weighted_generator(exponent, generator);
                assert!(!bool::from(entry.is_identity()));
                let doubled = pallas::Point::from(entry).double().to_affine();

                // Adjacent rows chain by doubling.
                if exponent + 1 < MERKLE_WORDS {
                    assert_eq!(
                        weighted.weighted_generator(exponent + 1, generator),
                        doubled
                    );
                }
            }
        }
    }
}
