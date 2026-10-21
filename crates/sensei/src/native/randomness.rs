//! Up-front sampling of the prover's entire randomness schedule.
//!
//! [`ProvingRandomness::sample`] draws every random value one proving run
//! will ever consume — in the exact order the committed RNG tapes pin — and
//! labels each value with the site that later spends it. The caller's source
//! is borrowed for sampling, which completes on the calling thread in
//! [`super::runtime::prove`]; worker stages retain no RNG reference. All
//! non-determinism is isolated here, and the rest of the pipeline is a pure
//! function of the request, the witness, and this structure. The golden proofs
//! are byte-exact: a value drawn out of order or spent at the wrong site changes
//! the proof bytes and fails the replay harness.
//!
//! Density of the schedule, in wide-uniform field samples (each sample
//! consumes eight tape `u64`s, reduced from 64 bytes):
//!
//! - per Action: 60 advice tail cells + 10 advice blinds + 42 lookup
//!   permutation tails/blinds + 18 permutation product tails/blinds +
//!   18 lookup product tails/blinds = 148 samples;
//! - per proof: 3 vanishing mask + 8 quotient blinds + 1 multiopen blind +
//!   12 IPA mask + 22 IPA round blinds = 46 samples.
//!
//! One Action consumes (148 + 46) · 8 = 1,552 `u64`s and two Actions
//! (2 · 148 + 46) · 8 = 2,736, the committed tape lengths.

use crate::{Error, RandomSource};
use alloc::vec::Vec;

use super::{
    field::Fp,
    generated_expressions::LOOKUPS,
    target::{
        ADVICE_COLUMNS, BLINDING_FACTORS, K, N, PERMUTATION_CHUNK_LEN, PERMUTATION_COLUMN_COUNT,
        QUOTIENT_PIECES, USABLE_ROWS_END,
    },
};

// Protocol facts: every count below is derived from the circuit dimensions and
// fixes the RNG schedule (1,552 `u64`s for one Action, 2,736 for two); none is
// a knob.

/// Rows `USABLE_ROWS_END..N` of every advice column are replaced by masks.
const ADVICE_TAIL_ROWS: usize = N - USABLE_ROWS_END;
/// Rows appended as the masking tail of each permuted lookup column.
const LOOKUP_TAIL_ROWS: usize = BLINDING_FACTORS + 1;
/// Lookup arguments per Action in the fixed circuit.
pub(crate) const LOOKUPS_PER_ACTION: usize = LOOKUPS.len();
/// Permutation grand-product sets per Action in the fixed circuit.
pub(crate) const PERMUTATION_SETS_PER_ACTION: usize =
    PERMUTATION_COLUMN_COUNT.div_ceil(PERMUTATION_CHUNK_LEN);
/// Recursive IPA rounds (`log2 N`), which is also the sparse mask's degree
/// count: one `alpha` per doubling exponent.
pub(crate) const IPA_ROUNDS: usize = K as usize;

/// The random values one Action's advice stage spends
/// (`ProverPrefix::commit_advice`).
pub(crate) struct AdviceRandomness {
    /// Mask values overwriting rows `USABLE_ROWS_END..N` of each advice
    /// column, column-major.
    pub(crate) column_tails: [[Fp; ADVICE_TAIL_ROWS]; ADVICE_COLUMNS],
    /// The commitment blind of each advice column, in column order.
    pub(crate) commitment_blinds: [Fp; ADVICE_COLUMNS],
}

/// Masks and blinds for one lookup's permuted input/table column pair
/// (`ProverPrefix::commit_lookup_permutations`).
#[derive(Clone, Copy)]
pub(crate) struct LookupBlinding {
    /// Mask values appended as the permuted input column's tail rows.
    pub(crate) input_rows: [Fp; LOOKUP_TAIL_ROWS],
    /// Mask values appended as the permuted table column's tail rows.
    pub(crate) table_rows: [Fp; LOOKUP_TAIL_ROWS],
    /// Commitment blind of the permuted input column.
    pub(crate) input_blind: Fp,
    /// Commitment blind of the permuted table column.
    pub(crate) table_blind: Fp,
}

/// Masks and blind for one permutation set's grand-product polynomial
/// (`ProverPrefix::commit_product_arguments`, permutation half).
#[derive(Clone, Copy)]
pub(crate) struct PermutationBlinding {
    /// Mask values overwriting the product column's last `BLINDING_FACTORS`
    /// rows.
    pub(crate) rows: [Fp; BLINDING_FACTORS],
    /// Commitment blind of the grand-product polynomial.
    pub(crate) blind: Fp,
}

/// Masks and blind for one lookup's grand-product polynomial
/// (`ProverPrefix::commit_product_arguments`, lookup half).
#[derive(Clone, Copy)]
pub(crate) struct ProductBlinding {
    /// Mask values overwriting the product column's last `BLINDING_FACTORS`
    /// rows.
    pub(crate) rows: [Fp; BLINDING_FACTORS],
    /// Commitment blind of the grand-product polynomial.
    pub(crate) blind: Fp,
}

/// The proof's linear vanishing mask r(X) = r_0 + r_1·X and its blind
/// (`ProverPrefix::commit_vanishing_random_polynomial`).
pub(crate) struct VanishingRandomness {
    /// The mask coefficients `[r_0, r_1]`, drawn in ascending degree order.
    pub(crate) mask: [Fp; 2],
    /// Commitment blind of the mask polynomial.
    pub(crate) blind: Fp,
}

/// The sparse IPA masking polynomial's coefficients and blind
/// (`ProverPrefix::commit_ipa_mask`).
pub(crate) struct IpaMaskRandomness {
    /// One coefficient per doubling exponent: `alphas[i]` sits at degree
    /// `2^i` of the sparse mask.
    pub(crate) alphas: [Fp; IPA_ROUNDS],
    /// Commitment blind of the sparse mask polynomial.
    pub(crate) blind: Fp,
}

/// The two commitment blinds one IPA round spends
/// (`ProverPrefix::finish_ipa`).
#[derive(Clone, Copy)]
pub(crate) struct IpaRoundBlinds {
    /// Blind of the round's `L` commitment.
    pub(crate) left: Fp,
    /// Blind of the round's `R` commitment.
    pub(crate) right: Fp,
}

/// Every random value one proving run consumes, drawn up front in the frozen
/// tape order and labeled by the stage that spends it.
pub(crate) struct ProvingRandomness {
    /// Advice tail masks and column blinds, one entry per Action.
    pub(crate) advice: Vec<AdviceRandomness>,
    /// Permuted lookup column masks and blinds, per Action and per lookup.
    pub(crate) lookup_permutations: Vec<[LookupBlinding; LOOKUPS_PER_ACTION]>,
    /// Permutation grand-product masks and blinds, per Action and per set.
    pub(crate) permutation_products: Vec<[PermutationBlinding; PERMUTATION_SETS_PER_ACTION]>,
    /// Lookup grand-product masks and blinds, per Action and per lookup.
    pub(crate) lookup_products: Vec<[ProductBlinding; LOOKUPS_PER_ACTION]>,
    /// The proof's linear vanishing mask and its blind.
    pub(crate) vanishing: VanishingRandomness,
    /// Commitment blind of each quotient piece, in piece order
    /// (`ProverPrefix::construct_quotient`).
    pub(crate) quotient_piece_blinds: [Fp; QUOTIENT_PIECES],
    /// Commitment blind of the collapsed multi-opening quotient `Q'`
    /// (`ProverPrefix::commit_multiopen_quotient`).
    pub(crate) multiopen_quotient_blind: Fp,
    /// The sparse IPA mask coefficients and blind.
    pub(crate) ipa_mask: IpaMaskRandomness,
    /// The `L`/`R` commitment blinds of each IPA round, in round order.
    pub(crate) ipa_rounds: [IpaRoundBlinds; IPA_ROUNDS],
}

impl ProvingRandomness {
    /// Draws the complete schedule for `action_count` Actions, consuming
    /// exactly `(148 · action_count + 46) · 8` tape `u64`s in the frozen
    /// order. The statement order below **is** the tape order; reordering any
    /// two draws changes the produced proofs.
    pub(crate) fn sample(rng: &mut dyn RandomSource, action_count: usize) -> Result<Self, Error> {
        let shape = crate::sizing::RequestShape::new(action_count)?;
        debug_assert_eq!(shape.random_words, (148 * action_count + 46) * 8);
        // Every per-Action container below is an inline array filled in
        // draw order; only the outer per-Action vectors scale with the
        // request.
        let mut advice = Vec::with_capacity(action_count);
        for _ in 0..action_count {
            let column_tails = sample_array([<Fp>::ZERO; ADVICE_TAIL_ROWS], || {
                sample_fp_array::<ADVICE_TAIL_ROWS>(rng)
            })?;
            let commitment_blinds = sample_fp_array::<ADVICE_COLUMNS>(rng)?;
            advice.push(AdviceRandomness {
                column_tails,
                commitment_blinds,
            });
        }

        let zero_lookup_blinding = LookupBlinding {
            input_rows: [<Fp>::ZERO; LOOKUP_TAIL_ROWS],
            table_rows: [<Fp>::ZERO; LOOKUP_TAIL_ROWS],
            input_blind: <Fp>::ZERO,
            table_blind: <Fp>::ZERO,
        };
        let mut lookup_permutations = Vec::with_capacity(action_count);
        for _ in 0..action_count {
            lookup_permutations.push(sample_array(zero_lookup_blinding, || {
                let input_rows = sample_fp_array::<LOOKUP_TAIL_ROWS>(rng)?;
                let table_rows = sample_fp_array::<LOOKUP_TAIL_ROWS>(rng)?;
                let input_blind = sample_fp(rng)?;
                let table_blind = sample_fp(rng)?;
                Ok(LookupBlinding {
                    input_rows,
                    table_rows,
                    input_blind,
                    table_blind,
                })
            })?);
        }

        let zero_permutation_blinding = PermutationBlinding {
            rows: [<Fp>::ZERO; BLINDING_FACTORS],
            blind: <Fp>::ZERO,
        };
        let mut permutation_products = Vec::with_capacity(action_count);
        for _ in 0..action_count {
            permutation_products.push(sample_array(zero_permutation_blinding, || {
                let rows = sample_fp_array::<BLINDING_FACTORS>(rng)?;
                let blind = sample_fp(rng)?;
                Ok(PermutationBlinding { rows, blind })
            })?);
        }

        let zero_product_blinding = ProductBlinding {
            rows: [<Fp>::ZERO; BLINDING_FACTORS],
            blind: <Fp>::ZERO,
        };
        let mut lookup_products = Vec::with_capacity(action_count);
        for _ in 0..action_count {
            lookup_products.push(sample_array(zero_product_blinding, || {
                let rows = sample_fp_array::<BLINDING_FACTORS>(rng)?;
                let blind = sample_fp(rng)?;
                Ok(ProductBlinding { rows, blind })
            })?);
        }

        let vanishing = {
            let constant = sample_fp(rng)?;
            let linear = sample_fp(rng)?;
            let blind = sample_fp(rng)?;
            VanishingRandomness {
                mask: [constant, linear],
                blind,
            }
        };

        let quotient_piece_blinds = sample_fp_array(rng)?;

        let multiopen_quotient_blind = sample_fp(rng)?;

        let ipa_mask = {
            let alphas = sample_fp_array(rng)?;
            let blind = sample_fp(rng)?;
            IpaMaskRandomness { alphas, blind }
        };

        let ipa_rounds = sample_array(
            IpaRoundBlinds {
                left: Fp::ZERO,
                right: Fp::ZERO,
            },
            || {
                let left = sample_fp(rng)?;
                let right = sample_fp(rng)?;
                Ok(IpaRoundBlinds { left, right })
            },
        )?;

        Ok(Self {
            advice,
            lookup_permutations,
            permutation_products,
            lookup_products,
            vanishing,
            quotient_piece_blinds,
            multiopen_quotient_blind,
            ipa_mask,
            ipa_rounds,
        })
    }
}

/// Draws `COUNT` field elements, in order, into an inline array. A failing
/// source stops at the failing draw exactly as the vector form does, so the
/// frozen schedule's partial consumption on failure is unchanged.
fn sample_fp_array<const COUNT: usize>(rng: &mut dyn RandomSource) -> Result<[Fp; COUNT], Error> {
    sample_array(<Fp>::ZERO, || sample_fp(rng))
}

/// Fills an inline array of `COUNT` values by calling `draw` once per slot,
/// in index order. The first failure returns immediately — later slots are
/// never drawn — so a failing source consumes exactly what the sequential
/// vector loops consumed. `placeholder` only pre-fills the array and is
/// never observable on success.
fn sample_array<T: Copy, const COUNT: usize>(
    placeholder: T,
    mut draw: impl FnMut() -> Result<T, Error>,
) -> Result<[T; COUNT], Error> {
    let mut values = [placeholder; COUNT];
    for value in &mut values {
        *value = draw()?;
    }
    Ok(values)
}

pub(crate) use crate::rng::sample_fp;

#[cfg(test)]
mod tests {
    use super::ProvingRandomness;
    use crate::{RandomnessError, rng::RandomSource};
    use std::prelude::v1::*;

    struct Counting {
        draws: usize,
    }

    impl RandomSource for Counting {
        fn next_u64(&mut self) -> Result<u64, RandomnessError> {
            self.draws += 1;
            Ok(self.draws as u64)
        }
    }

    /// The schedule's total draw count is frozen protocol behavior; these are
    /// the committed tape lengths the golden harness replays.
    #[test]
    fn schedule_matches_committed_tape_lengths() {
        for (action_count, expected_u64_draws) in [(1, 1_552), (2, 2_736)] {
            let mut rng = Counting { draws: 0 };
            ProvingRandomness::sample(&mut rng, action_count).unwrap();
            assert_eq!(rng.draws, expected_u64_draws);
        }
    }

    /// A source that fails mid-schedule surfaces `RngFailure` without
    /// panicking, regardless of where in the schedule it dies.
    #[test]
    fn exhausted_source_reports_rng_failure() {
        struct Budget {
            remaining: usize,
        }
        impl RandomSource for Budget {
            fn next_u64(&mut self) -> Result<u64, RandomnessError> {
                if self.remaining == 0 {
                    return Err(RandomnessError);
                }
                self.remaining -= 1;
                Ok(0)
            }
        }
        for budget in [0, 7, 8, 480, 1_551] {
            let mut rng = Budget { remaining: budget };
            assert!(matches!(
                ProvingRandomness::sample(&mut rng, 1),
                Err(crate::Error::RngFailure)
            ));
        }
    }
}
