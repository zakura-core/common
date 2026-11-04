//! Advice masking and commitments: the first challenge-producing proof stage.
//!
//! This stage consumes the already-checked witness matrices and the labeled advice
//! randomness. The ordered transcript writes follow the batched commitments.

use crate::Error;
use crate::native::commitment::normalized;
use crate::native::polynomial::SharedPoly;
use crate::native::randomness::AdviceRandomness;
use crate::native::regions::{sinsemilla_hashes, variable_base_mul};
use crate::native::target::{ADVICE_COLUMNS, USABLE_ROWS_END};
use alloc::{sync::Arc, vec::Vec};

use super::inventory::advice_stage;
use super::{AdviceMatrix, AdvicePrefix, ProverPrefix, support_excludes_tail};

impl ProverPrefix<'_> {
    /// Installs the pre-sampled advice tail masks and commitment blinds,
    /// writes every advice commitment in proof order, and squeezes `theta`.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** no challenge: the transcript holds only the fixed VK
    ///   representative and the instance commitments absorbed by
    ///   [`Self::initialize_checked`].
    /// - **Publishes** every Action's advice column commitments, Action-major
    ///   and column-ascending (`ADVICE_COLUMNS` per Action), from one
    ///   Lagrange-basis commitment batch.
    /// - **Squeezes** `θ`, the lookup compression challenge, carried on the
    ///   returned [`AdvicePrefix`].
    /// - **Draws** no randomness: the tail masks (rows `USABLE_ROWS_END..N`
    ///   of every column) and the commitment blinds arrive pre-sampled and
    ///   are only installed here, in column order.
    ///
    /// Preparation is the mask installation and the batch; the write loop is
    /// the only transcript-ordered section and follows the batch's job order.
    ///
    /// # Work and buffer inventory
    ///
    /// Logical counts, in field elements, from [`advice_stage`]. Per Action:
    /// `COLUMNS_PER_ACTION` finalized columns arrive from the witness builder
    /// (already checked by preflight); each has its
    /// `MASKED_ROWS_PER_COLUMN` tail rows overwritten in place by pre-sampled
    /// masks, then one logical `N`-scalar Lagrange-basis commitment in the stage's
    /// single batch. The `FOLDED_COLUMNS_PER_ACTION` coordinate columns of
    /// the variable-base gadget commit through a batch-lifetime copy with
    /// their `FOLDED_RUN_CELLS`-cell run zeroed plus one fixed-base term for
    /// the run; the `WORD_COLUMNS_PER_ACTION` Sinsemilla running-sum
    /// columns commit through a batch-lifetime copy with their
    /// `WORD_CELLS_PER_ACTION` cells zeroed plus one MSM of
    /// `WORD_CELLS_PER_ACTION + WORD_PIECES_PER_ACTION` small scalars over
    /// transposed word bases. The target applies further carve-outs
    /// described by its commitment plan, then groups equal nonzero residual
    /// scalars by summing their bases. Those grouped bases and scalars live
    /// only through the batch. Alive at return per Action: `RETAINED_PER_ACTION`
    /// elements, the columns themselves, plus `COLUMNS_PER_ACTION` blinds.
    pub(crate) fn commit_advice(
        &mut self,
        matrices: Vec<Arc<AdviceMatrix>>,
        randomness: Vec<AdviceRandomness>,
    ) -> Result<AdvicePrefix, Error> {
        if matrices.len() != self.instance_polynomials.len() || randomness.len() != matrices.len() {
            return Err(Error::InternalInvariant);
        }

        let mut values = Vec::with_capacity(matrices.len());
        let mut blinds = Vec::with_capacity(matrices.len());
        for (matrix, action_randomness) in matrices.into_iter().zip(randomness) {
            let AdviceRandomness {
                column_tails,
                commitment_blinds,
            } = action_randomness;
            // Preflight has finished with the matrix, so this recovers the
            // columns without a copy.
            let AdviceMatrix {
                mut columns,
                support,
            } = Arc::try_unwrap(matrix).unwrap_or_else(|shared| (*shared).clone());
            // Support contract at the commitment boundary: the masks installed
            // below cover no supported cell, so a support-gathering commitment
            // path may treat the tail rows as its own separate contribution.
            if columns.len() != ADVICE_COLUMNS || !support_excludes_tail(&support) {
                return Err(Error::InternalInvariant);
            }
            for (column, tail) in columns.iter_mut().zip(column_tails) {
                let masked = column
                    .get_mut(USABLE_ROWS_END..)
                    .ok_or(Error::InternalInvariant)?;
                // Inventory tie: the masked tail is exactly the blinding rows.
                if masked.len() != tail.len() || tail.len() != advice_stage::MASKED_ROWS_PER_COLUMN
                {
                    return Err(Error::InternalInvariant);
                }
                masked.copy_from_slice(&tail);
            }
            values.push(columns.into_iter().map(SharedPoly::new).collect::<Vec<_>>());
            blinds.push(commitment_blinds);
        }

        let target = self.target;
        // Each job names its advice column: the target selects the column's
        // carve-outs from the shared layout and checks their premises before
        // grouping equal residual coefficients.
        let jobs = values
            .iter()
            .zip(&blinds)
            .flat_map(|(columns, action_blinds)| {
                columns
                    .iter()
                    .zip(action_blinds)
                    .enumerate()
                    .map(|(column, (scalars, blind))| (scalars, blind, column))
            })
            .collect::<Vec<_>>();
        // Inventory ties: each commitment consumes one logical `N`-scalar
        // column, `ADVICE_COLUMNS` per Action. The folded-coordinate and
        // Sinsemilla-word subsets have the expected column counts.
        if jobs.len() != advice_stage::commitment_jobs(values.len())
            || jobs
                .iter()
                .any(|(column, _, _)| column.len() != advice_stage::COMMITMENT_SCALARS_PER_COLUMN)
            || jobs
                .iter()
                .filter(|(_, _, column)| {
                    variable_base_mul::COORDINATE_COLUMNS.contains(column)
                        || sinsemilla_hashes::RUNNING_SUM_COLUMNS.contains(column)
                })
                .count()
                != values.len()
                    * (advice_stage::FOLDED_COLUMNS_PER_ACTION
                        + advice_stage::WORD_COLUMNS_PER_ACTION)
        {
            return Err(Error::InternalInvariant);
        }
        // The inventory/support checks above establish the prepared advice
        // layout; a commitment error breaks that internal representation.
        let pending_commitments = target
            .parameters()
            .commit_advice_batch_projective(&jobs, &mut self.workspace.msm, self.execution)
            .map_err(|_| Error::InternalInvariant)?;

        // Blinded commitments can be identity; transcript rejection needs a
        // new proof attempt with fresh draws, not a different witness.
        let mut normalized = normalized(&pending_commitments).into_iter();
        for _ in &values {
            for _ in 0..ADVICE_COLUMNS {
                let commitment = normalized.next().ok_or(Error::InternalInvariant)?;
                self.transcript
                    .write_point(&commitment)
                    .map_err(|_| Error::RetryRandomness)?;
            }
        }
        if normalized.next().is_some() {
            return Err(Error::InternalInvariant);
        }
        let theta = self.transcript.squeeze_challenge();

        Ok(AdvicePrefix {
            values,
            blinds,
            theta,
        })
    }
}
