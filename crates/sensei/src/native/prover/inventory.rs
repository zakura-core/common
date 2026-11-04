//! Compile-time work and buffer counts for the proof stages.
//!
//! The stage implementations assert logical dimensions against these values.
//! Counts describe logical work, not allocator usage or peak resident memory.

use crate::native::generated_expressions;
use crate::native::regions::{sinsemilla_hashes, variable_base_mul};
use crate::native::target::{
    ADVICE_COLUMNS, BLINDING_FACTORS, EXTENDED_N, K, N, PERMUTATION_SETS, QUOTIENT_PIECES,
    USABLE_ROWS_END,
};

use super::FOLD_CHUNK_ROWS;

/// Logical work and buffer counts for product construction.
///
/// Used by [`ProverPrefix::commit_product_arguments`][products]. Counts are in
/// field elements, not bytes or allocator usage. Coset counts describe expanded
/// products; multi-window proofs defer those allocations to the quotient stage.
///
/// [products]: crate::native::prover::ProverPrefix::commit_product_arguments
pub(crate) mod product_stage {
    use super::{EXTENDED_N, N, PERMUTATION_SETS, generated_expressions::LOOKUPS};

    /// Grand products constructed per Action: one per permutation set plus
    /// one per lookup argument.
    pub(crate) const PRODUCTS_PER_ACTION: usize = PERMUTATION_SETS + LOOKUPS.len();
    /// Rows of each product's committed Lagrange column. Lookup products
    /// commit as one `N`-term MSM against the Lagrange SRS; permutation sets
    /// commit by interval against the prefix-sum table — one term per scan
    /// run (structurally about 273, 630, and 7 for the three sets) plus the
    /// six-row tail. Each carries a blind on the blinding generator.
    pub(crate) const COMMITMENT_SCALARS_PER_PRODUCT: usize = N;
    /// Elements copied once per product out of its Lagrange column into the
    /// transform side job (the copy becomes the coefficient buffer; the
    /// original is dropped when the forms are installed).
    pub(crate) const STAGED_COPY_PER_PRODUCT: usize = N;
    /// Elements each product's base-domain inverse transform (Lagrange →
    /// coefficients) works over.
    pub(crate) const INVERSE_TRANSFORM_PER_PRODUCT: usize = N;
    /// Elements each full-width permutation set's and each lookup product's
    /// coefficient → extended-coset expansion produces.
    pub(crate) const COSET_PER_EXTENDED_PRODUCT: usize = EXTENDED_N;
    /// Elements the singleton permutation set's expansion produces: its
    /// every fold consumer is a 2N or N term
    /// (`fold_order::permutation_product_class`), so its coset is the 2N
    /// class coset — the extended coset's stride-4 rows.
    pub(crate) const COSET_PER_SINGLETON_PRODUCT: usize = 2 * N;
    /// Retained elements per Action when products include their expanded cosets.
    ///
    /// Counts `N` coefficients per product and their class cosets. Deferred
    /// products retain only `PRODUCTS_PER_ACTION * N` coefficients at this
    /// stage. Coefficients survive for openings; cosets die after the fold.
    pub(crate) const RETAINED_PER_ACTION: usize = PRODUCTS_PER_ACTION * N
        + (PRODUCTS_PER_ACTION - 1) * COSET_PER_EXTENDED_PRODUCT
        + COSET_PER_SINGLETON_PRODUCT;

    /// Total commitment jobs and coefficient-transform side jobs for a request.
    /// Admission can split this work into bounded batches.
    pub(crate) const fn commitment_jobs(action_count: usize) -> usize {
        action_count * PRODUCTS_PER_ACTION
    }

    const _: () = {
        assert!(
            RETAINED_PER_ACTION
                == PRODUCTS_PER_ACTION * INVERSE_TRANSFORM_PER_PRODUCT
                    + (PRODUCTS_PER_ACTION - 1) * COSET_PER_EXTENDED_PRODUCT
                    + COSET_PER_SINGLETON_PRODUCT
        );
        assert!(COSET_PER_SINGLETON_PRODUCT * 4 == COSET_PER_EXTENDED_PRODUCT);
        assert!(STAGED_COPY_PER_PRODUCT == COMMITMENT_SCALARS_PER_PRODUCT);
        assert!(PRODUCTS_PER_ACTION == 6);
    };
}

/// Static work and live-buffer inventory of the advice stage
/// ([`ProverPrefix::commit_advice`](crate::native::prover::ProverPrefix::commit_advice)), in **logical field elements** derived
/// from the circuit dimensions; conventions as for [`product_stage`].
pub(crate) mod advice_stage {
    use super::{ADVICE_COLUMNS, N, USABLE_ROWS_END};

    /// Columns committed per Action, `N` rows each.
    pub(crate) const COLUMNS_PER_ACTION: usize = ADVICE_COLUMNS;
    /// Rows of every column overwritten by pre-sampled masks before
    /// commitment (the blinding tail).
    pub(crate) const MASKED_ROWS_PER_COLUMN: usize = N - USABLE_ROWS_END;
    /// Logical scalars in each column's Lagrange-basis commitment. Carve-outs
    /// and grouping equal residual coefficients reduce the executed MSM;
    /// every column still carries its own blind.
    pub(crate) const COMMITMENT_SCALARS_PER_COLUMN: usize = N;
    /// Columns per Action whose commitment folds the variable-base gadget's
    /// repeated coordinate run into one extra fixed-base term: the run's
    /// `FOLDED_RUN_CELLS` scalars are committed as zero in the MSM.
    pub(crate) const FOLDED_COLUMNS_PER_ACTION: usize =
        super::variable_base_mul::COORDINATE_COLUMNS.len();
    /// Equal cells in each folded run.
    pub(crate) const FOLDED_RUN_CELLS: usize = super::variable_base_mul::INCOMPLETE_LO_BITS;
    /// Columns per Action (2 and 7) whose commitment transposes the
    /// Sinsemilla running sums onto ten-bit word bases: their
    /// `WORD_CELLS_PER_ACTION` cells are committed as zero in the dense MSM
    /// and as `WORD_CELLS_PER_ACTION + WORD_PIECES_PER_ACTION` small scalars
    /// in the word MSMs.
    pub(crate) const WORD_COLUMNS_PER_ACTION: usize =
        super::sinsemilla_hashes::RUNNING_SUM_COLUMNS.len();
    /// Running-sum cells per Action across every Sinsemilla hash.
    pub(crate) const WORD_CELLS_PER_ACTION: usize = super::sinsemilla_hashes::WORD_COUNT;
    /// Sinsemilla message pieces per Action, one remainder term each.
    pub(crate) const WORD_PIECES_PER_ACTION: usize = super::sinsemilla_hashes::PIECE_COUNT;
    /// Elements alive per Action when the stage returns: the `N`-row
    /// Lagrange columns themselves, uncopied (final consumers: the lookup and
    /// product stages read them; the quotient stage's transforms take them
    /// over).
    pub(crate) const RETAINED_PER_ACTION: usize = COLUMNS_PER_ACTION * N;

    /// Commitment jobs in the stage's single batch for `action_count`
    /// Actions.
    pub(crate) const fn commitment_jobs(action_count: usize) -> usize {
        action_count * COLUMNS_PER_ACTION
    }

    const _: () = {
        assert!(MASKED_ROWS_PER_COLUMN == super::BLINDING_FACTORS + 1);
        assert!(RETAINED_PER_ACTION == COLUMNS_PER_ACTION * COMMITMENT_SCALARS_PER_COLUMN);
        assert!(FOLDED_COLUMNS_PER_ACTION + WORD_COLUMNS_PER_ACTION <= COLUMNS_PER_ACTION);
        assert!(WORD_CELLS_PER_ACTION == 1_933 && WORD_PIECES_PER_ACTION == 116);
        assert!(
            FOLDED_RUN_CELLS
                == super::variable_base_mul::COORDINATE_LOCAL_ROWS.end
                    - super::variable_base_mul::COORDINATE_LOCAL_ROWS.start
        );
    };
}

/// Static work and live-buffer inventory of the lookup-permutation stage
/// ([`ProverPrefix::commit_lookup_permutations`](crate::native::prover::ProverPrefix::commit_lookup_permutations)), in **logical field
/// elements**; conventions as for [`product_stage`]. Run counts of the
/// permuted columns are witness-dependent and therefore not constants here.
pub(crate) mod lookup_stage {
    use super::{BLINDING_FACTORS, N, USABLE_ROWS_END, generated_expressions::LOOKUPS};

    /// Lookup arguments per Action, each producing one (input, table) pair.
    pub(crate) const LOOKUPS_PER_ACTION: usize = LOOKUPS.len();
    /// `θ`-compressed table columns, `N` rows each, prepared once per proof
    /// and shared by every Action (final consumer: the product stage).
    pub(crate) const SHARED_TABLE_COLUMNS: usize = LOOKUPS.len();
    /// `N`-row columns alive per (Action, lookup) pair at return: the
    /// compressed input, the permuted input, and the permuted table (final
    /// consumers: the product stage reads all three; the quotient stage's
    /// transforms take over the two permuted columns).
    pub(crate) const COLUMNS_PER_PAIR: usize = 3;
    /// Rows each pair permutes (sorted or reconstructed from the prepared
    /// table order): the usable region.
    pub(crate) const PERMUTED_ROWS_PER_PAIR: usize = USABLE_ROWS_END;
    /// Pre-sampled mask rows appended to each permuted column.
    pub(crate) const MASK_ROWS_PER_COLUMN: usize = BLINDING_FACTORS + 1;
    /// Commitments per pair (permuted input, permuted table), each through
    /// the interval batch: one MSM term per run boundary of the piecewise-
    /// constant usable prefix plus the `MASK_ROWS_PER_COLUMN`-row dense tail,
    /// or the dense `N`-term fallback.
    pub(crate) const COMMITMENTS_PER_PAIR: usize = 2;
    /// Elements alive per pair when the stage returns.
    pub(crate) const RETAINED_PER_PAIR: usize = COLUMNS_PER_PAIR * N;

    /// Commitment jobs in the stage's single batch for `action_count`
    /// Actions.
    pub(crate) const fn commitment_jobs(action_count: usize) -> usize {
        action_count * LOOKUPS_PER_ACTION * COMMITMENTS_PER_PAIR
    }

    const _: () = {
        assert!(PERMUTED_ROWS_PER_PAIR + MASK_ROWS_PER_COLUMN == N);
        assert!(RETAINED_PER_PAIR == COLUMNS_PER_PAIR * N);
        assert!(SHARED_TABLE_COLUMNS == LOOKUPS_PER_ACTION);
    };
}

/// Logical work and buffer counts for quotient construction.
///
/// Used by [`ProverPrefix::construct_quotient`][construct]; conventions as for
/// [`product_stage`]. Fold tasks, accumulators, and interpolation are per window;
/// piece commitments are per proof. Per-Action opening storage survives across
/// windows, so these counts do not imply a bound on total request memory.
///
/// [construct]: crate::native::prover::ProverPrefix::construct_quotient
pub(crate) mod quotient_stage {
    use super::{
        ADVICE_COLUMNS, EXTENDED_N, FOLD_CHUNK_ROWS, N, QUOTIENT_PIECES,
        generated_expressions::LOOKUPS,
    };

    /// Dense Lagrange columns per Action transformed here to `N`
    /// coefficients and a coset (one inverse transform and one expansion
    /// each): advice expands to 8N, both permuted columns of every lookup
    /// to 4N. The instance column takes the prepared sparse coset path instead.
    pub(crate) const DENSE_TRANSFORMS_PER_ACTION: usize = ADVICE_COLUMNS + 2 * LOOKUPS.len();
    /// Permuted lookup columns among those, transferred out of the lookup
    /// records (never copied).
    pub(crate) const PERMUTED_TRANSFORMS_PER_ACTION: usize = 2 * LOOKUPS.len();
    /// Row tasks per window of the fused degree-classed fold: one pass over the
    /// `EXTENDED_N` extended rows, each task owning `FOLD_CHUNK_ROWS` rows
    /// and the matching stride views of every class accumulator.
    pub(crate) const FOLD_TASKS: usize = EXTENDED_N / FOLD_CHUNK_ROWS;
    /// Elements of the divided accumulators one window emits (the 8N, 4N,
    /// 2N, and N classes and the separate 4N lookup branch).
    pub(crate) const CLASS_ACCUMULATOR_ELEMENTS: usize =
        EXTENDED_N + EXTENDED_N / 2 + EXTENDED_N / 4 + EXTENDED_N / 8 + EXTENDED_N / 2;
    /// Coefficients the interpolation produces: the quotient split into
    /// `QUOTIENT_PIECES` pieces of `N`.
    pub(crate) const QUOTIENT_COEFFICIENTS: usize = QUOTIENT_PIECES * N;
    /// Coefficient-basis commitments published, one `N`-scalar MSM each.
    pub(crate) const PIECE_COMMITMENTS: usize = QUOTIENT_PIECES;
    /// Coefficient buffers alive per Action when the stage returns, for the
    /// openings: advice and permuted lookup coefficients (`N`
    /// each). Expanded cosets are released after their last fold reader;
    /// interpolation and commitments can overlap that release.
    pub(crate) const RETAINED_COEFFICIENTS_PER_ACTION: usize =
        (ADVICE_COLUMNS + 2 * LOOKUPS.len()) * N;

    /// Permuted-column transforms staged for `action_count` Actions.
    pub(crate) const fn permuted_transforms(action_count: usize) -> usize {
        action_count * PERMUTED_TRANSFORMS_PER_ACTION
    }

    const _: () = {
        assert!(EXTENDED_N.is_multiple_of(FOLD_CHUNK_ROWS));
        assert!(DENSE_TRANSFORMS_PER_ACTION == ADVICE_COLUMNS + PERMUTED_TRANSFORMS_PER_ACTION);
        assert!(RETAINED_COEFFICIENTS_PER_ACTION == DENSE_TRANSFORMS_PER_ACTION * N);
        assert!(CLASS_ACCUMULATOR_ELEMENTS == 19 * N);
        assert!(FOLD_TASKS == 128 && PIECE_COMMITMENTS == 8);
    };
}

/// Static work and live-buffer inventory of the evaluation and multi-opening
/// stages ([`ProverPrefix::write_evaluations`](crate::native::prover::ProverPrefix::write_evaluations),
/// [`ProverPrefix::commit_multiopen_quotient`](crate::native::prover::ProverPrefix::commit_multiopen_quotient),
/// [`ProverPrefix::commit_ipa_mask`](crate::native::prover::ProverPrefix::commit_ipa_mask)), in **logical field elements**;
/// conventions as for [`product_stage`].
pub(crate) mod opening_stage {
    use super::{N, PERMUTATION_SETS, generated_expressions::LOOKUPS};
    use crate::native::queries::{ADVICE_QUERIES, FIXED_QUERIES, INSTANCE_QUERIES};
    use sensei_shared::PERMUTATION_COLUMN_COUNT;

    /// Evaluations published once per proof: the fixed queries, the
    /// vanishing mask at `x`, and the sigma columns at `x`.
    pub(crate) const EVALUATIONS_FIXED: usize = FIXED_QUERIES.len() + 1 + PERMUTATION_COLUMN_COUNT;
    /// Evaluations published per Action: its instance and advice queries,
    /// each permutation set at `x` and `x·ω` plus the `x_last` opening of
    /// every set but the last, and each lookup's five openings.
    pub(crate) const EVALUATIONS_PER_ACTION: usize = INSTANCE_QUERIES.len()
        + ADVICE_QUERIES.len()
        + (2 * PERMUTATION_SETS + PERMUTATION_SETS - 1)
        + 5 * LOOKUPS.len();
    /// Distinct point sets of the fixed opening schedule (independent of the
    /// Action count — more Actions repeat the same sets): one `Q_i` of `N`
    /// coefficients is materialized, divided, and later evaluated per set.
    pub(crate) const POINT_SETS: usize = crate::native::protocol::POINT_SETS;
    /// `N`-coefficient polynomials the multi-opening stage retains for the
    /// IPA: the `Q_i` and `Q'`.
    pub(crate) const RETAINED_POLYNOMIALS: usize = POINT_SETS + 1;

    /// Evaluation scalars written for `action_count` Actions, each one dense
    /// `N`-coefficient evaluation using cached powers except the linear mask
    /// and the ten-value instance prefixes evaluated with shared Lagrange weights.
    pub(crate) const fn evaluations(action_count: usize) -> usize {
        EVALUATIONS_FIXED + action_count * EVALUATIONS_PER_ACTION
    }

    const _: () = {
        assert!(EVALUATIONS_FIXED == 45 && EVALUATIONS_PER_ACTION == 49);
        assert!(RETAINED_POLYNOMIALS * N == 6 * N);
    };
}

/// Static work inventory of the IPA finish ([`ProverPrefix::finish_ipa`](crate::native::prover::ProverPrefix::finish_ipa));
/// conventions as for [`product_stage`].
pub(crate) mod ipa_stage {
    use super::{K, N};

    /// Rounds, each halving the folded polynomial.
    pub(crate) const ROUNDS: usize = K as usize;
    /// Index-selected MSMs per round (`L` and `R`), each over the current
    /// logical half-length, plus one fixed-base value term and one blind term
    /// each. Materializing after rounds 3 and 6 reduces the physical MSMs from
    /// 1024 terms to 128, then 16; folds between those boundaries stay virtual.
    pub(crate) const MSMS_PER_ROUND: usize = 2;
    /// Elements of the folded polynomial entering round `j` (`N >> j`); it
    /// shrinks in place, so the live buffer is the round-0 size.
    pub(crate) const FOLDED_POLYNOMIAL: usize = N;

    /// Logical terms in each of round `round`'s two commitments.
    pub(crate) const fn round_terms(round: usize) -> usize {
        FOLDED_POLYNOMIAL >> (round + 1)
    }

    const _: () = {
        assert!(ROUNDS == 11 && MSMS_PER_ROUND == 2);
        assert!(round_terms(0) == N / 2 && round_terms(ROUNDS - 1) == 1);
    };
}
