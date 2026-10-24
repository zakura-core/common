//! Blinded commitments over the fixed coefficient and Lagrange SRS.
//!
//! Dense batches and structured advice/interval paths share the same generators
//! and blind terms. Structured bases are prepared from the circuit footprint;
//! runtime scalars, blinding tails, and batch scheduling stay with each job.
//!
//! The [`preparation`] child holds circuit-specific basis recipes. Their
//! composition and runtime commitment jobs stay together in this module.

use alloc::sync::Arc;
use alloc::vec::Vec;
use sensei_shared::fixed_bases::FIXED_BASE_WINDOW_SIZE;
use sensei_shared::{K, N, USABLE_ROWS_END};
use udon::msm::Bases;

use crate::native::buffer::Buffer;
#[cfg(test)]
use crate::native::commitment::sum_prepared;
use crate::native::commitment::{
    CommitmentTerm, FixedGenerator, FoldingGenerators, MsmWorkspace, execute_terms,
    execute_with_side_jobs, normalized,
};
use crate::native::curve::{PreparedAffinePoint, Vesta, VestaAffine, VestaPoint, VestaProjective};
use crate::native::field::Fp;
use crate::native::polynomial::SharedPoly;
use crate::native::regions::{
    fixed_base_running_sums, fixed_base_windows, range_running_sums, sinsemilla_hashes,
    variable_base_mul,
};
use crate::native::srs::{PREPARED_POINTS, PreparedSrs};
use crate::native::storage::Column;
use crate::native::worker::Execution;

use super::{
    FIXED_WINDOW_U_BASES, FIXED_WINDOW_X_BASES, FIXED_WINDOW_Y_BASES, Parameters, TargetError,
};

mod grouped;
pub(super) use grouped::ResidualCopies;
mod lookup;
pub(crate) use lookup::{LookupCommitPair, SuffixGenerators};
mod preparation;
use preparation::{
    prepare_bit_bases, prepare_constant_columns, prepare_repeated_coordinate_base,
    prepare_window_selection, prepare_word_bases,
};

impl Parameters {
    /// Borrows shared SRS preparation and owns circuit-specific structured bases.
    pub(super) fn over_srs(
        srs: Arc<PreparedSrs>,
        windows: &[[sensei_shared::WindowTableEntry; 8]],
        copy_classes: &super::copy_constraints::CopyClasses,
    ) -> Result<Self, TargetError> {
        let prepare = |bases: &[VestaAffine]| {
            bases
                .iter()
                .map(PreparedAffinePoint::from_affine)
                .collect::<Vec<_>>()
        };
        let points = PREPARED_POINTS;
        let lagrange_generators = &srs.lagrange_generators;
        let lagrange_prefix_sums = prepare(&points.lagrange_prefix_sums);
        let repeated_coordinate_base = prepare_repeated_coordinate_base(&lagrange_prefix_sums)?;
        let mut word_bases = prepare_word_bases(
            lagrange_generators,
            sinsemilla_hashes::pieces(),
            sinsemilla_hashes::WORD_BITS,
            sinsemilla_hashes::PIECE_COUNT,
            sinsemilla_hashes::WORD_COUNT,
        )?;
        let fixed_word_bases = prepare_word_bases(
            lagrange_generators,
            fixed_base_running_sums::pieces(),
            fixed_base_running_sums::WORD_BITS,
            fixed_base_running_sums::PIECE_COUNT,
            fixed_base_running_sums::WORD_COUNT,
        )?;
        let range_word_bases = prepare_word_bases(
            lagrange_generators,
            range_running_sums::pieces(),
            range_running_sums::WORD_BITS,
            range_running_sums::PIECE_COUNT,
            range_running_sums::WORD_COUNT,
        )?;
        word_bases.reserve_exact(fixed_word_bases.len() + range_word_bases.len());
        word_bases.extend(fixed_word_bases);
        word_bases.extend(range_word_bases);
        let bit_bases = prepare_bit_bases(lagrange_generators)?;
        let copied_columns = word_bases
            .iter()
            .map(|bases| bases.column)
            .chain(bit_bases.iter().map(|bases| bases.column))
            .chain(variable_base_mul::COORDINATE_COLUMNS)
            .chain([fixed_base_windows::U_COLUMN])
            .collect::<Vec<_>>();
        let constant_columns = prepare_constant_columns(lagrange_generators, &copied_columns)?;
        // A word-transposed column may also carry bit chains (column 9: the
        // range streams and the variable-base hi chain live in different
        // regions); every carve-out's cells must nevertheless be distinct.
        let residual_copies = {
            let window_rows = fixed_base_windows::window_rows();
            // Structural census, sized exactly from the carve-out extents.
            let cell_count = word_bases
                .iter()
                .flat_map(|bases| &bases.pieces)
                .map(|(rows, _)| rows.len())
                .sum::<usize>()
                + bit_bases
                    .iter()
                    .flat_map(|bases| &bases.chains)
                    .map(|(rows, _)| rows.len())
                    .sum::<usize>()
                + constant_columns
                    .iter()
                    .map(|constants| constants.cells.len())
                    .sum::<usize>()
                + variable_base_mul::coordinate_rows().len()
                    * variable_base_mul::COORDINATE_COLUMNS.len()
                + window_rows.len() * 3;
            let mut cells: Vec<(usize, usize)> = Vec::with_capacity(cell_count);
            for bases in &word_bases {
                for (rows, _) in &bases.pieces {
                    cells.extend(rows.clone().map(|row| (bases.column, row)));
                }
            }
            for bases in &bit_bases {
                for (rows, _) in &bases.chains {
                    cells.extend(rows.iter().map(|row| (bases.column, *row)));
                }
            }
            for constants in &constant_columns {
                cells.extend(
                    constants
                        .cells
                        .iter()
                        .map(|(row, _)| (constants.column, *row)),
                );
            }
            for row in variable_base_mul::coordinate_rows() {
                cells.extend(variable_base_mul::COORDINATE_COLUMNS.map(|column| (column, row)));
            }
            for row in window_rows {
                for column in [
                    fixed_base_windows::X_COLUMN,
                    fixed_base_windows::Y_COLUMN,
                    fixed_base_windows::U_COLUMN,
                ] {
                    cells.push((column, row));
                }
            }
            cells.sort_unstable();
            if cells.windows(2).any(|pair| pair[0] == pair[1]) {
                return Err(TargetError::Malformed);
            }
            ResidualCopies::new(lagrange_generators, copy_classes, &cells)?
        };
        // Each column carries at most one word transposition.
        let mut word_columns = word_bases
            .iter()
            .map(|bases| bases.column)
            .collect::<Vec<_>>();
        word_columns.sort_unstable();
        if word_columns.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(TargetError::Malformed);
        }
        let window_selections = alloc::vec![
            prepare_window_selection(
                windows,
                fixed_base_windows::X_COLUMN,
                FIXED_WINDOW_X_BASES,
                |entry| entry.x,
            )?,
            prepare_window_selection(
                windows,
                fixed_base_windows::Y_COLUMN,
                FIXED_WINDOW_Y_BASES,
                |entry| entry.y,
            )?,
            prepare_window_selection(
                windows,
                fixed_base_windows::U_COLUMN,
                FIXED_WINDOW_U_BASES,
                |entry| entry.u,
            )?,
        ];
        // The structured column plans must be disjoint: a column is folded,
        // word-transposed, or dense, never two of these.
        if word_bases
            .iter()
            .any(|bases| variable_base_mul::COORDINATE_COLUMNS.contains(&bases.column))
        {
            return Err(TargetError::Malformed);
        }
        let config = crate::tuning::COMMITMENT_TABLES;
        let sorted_lookup_suffixes = SuffixGenerators::new(lagrange_generators)?;
        let mut parameters = Self {
            srs,
            folding_generators: FoldingGenerators::new(&points.coefficient_bases),
            sparse_mask_generators: if config.sparse.is_some() {
                (0..11)
                    .map(|i| FixedGenerator::configured(&points.coefficient_bases[1 << i], 6 + i))
                    .collect()
            } else {
                Vec::new()
            },
            sorted_lookup_suffixes,
            lagrange_prefix_sums,

            residual_copies,
            repeated_coordinate_base,
            word_bases,
            bit_bases,
            constant_columns,
            window_selections,
            advice_carveouts: core::array::from_fn(|_| Vec::new()),
            prepared_first_coefficient_generator: FixedGenerator::configured(
                &points.coefficient_bases[0],
                4,
            ),
        };
        parameters.advice_carveouts =
            core::array::from_fn(|column| parameters.prepare_advice_column_carveouts(column));
        Ok(parameters)
    }

    #[cfg(test)]
    pub(crate) fn coefficient_generators(&self) -> &[PreparedAffinePoint<Vesta>] {
        &self.srs.coefficient_generators
    }

    #[cfg(all(test, feature = "verifier"))]
    pub(crate) fn shared_srs(&self) -> &Arc<PreparedSrs> {
        &self.srs
    }

    // Coefficient commitments and IPA rounds share the selected expansion.
    pub(crate) fn quotient_coefficient_bases(&self) -> Bases<'_, Vesta> {
        self.coefficient_bases()
    }

    pub(crate) fn coefficient_bases(&self) -> Bases<'_, Vesta> {
        self.srs.coefficient_bases()
    }

    pub(crate) fn folding_bases(&self) -> Bases<'_, Vesta> {
        self.folding_generators.bases(self.coefficient_bases())
    }

    fn lagrange_bases(&self) -> Bases<'_, Vesta> {
        self.srs.lagrange_bases()
    }

    #[cfg(test)]
    pub(crate) fn blind_generator(&self) -> &VestaAffine {
        &PREPARED_POINTS.blind_generator
    }

    #[cfg(test)]
    pub(crate) fn ipa_generator(&self) -> &VestaAffine {
        &PREPARED_POINTS.ipa_generator
    }

    pub(crate) fn prepared_blind_generator(&self) -> &FixedGenerator {
        &self.srs.blind_generator
    }

    pub(crate) fn prepared_ipa_generator(&self) -> &FixedGenerator {
        &self.srs.ipa_generator
    }

    pub(crate) fn prepared_first_coefficient_generator(&self) -> &FixedGenerator {
        &self.prepared_first_coefficient_generator
    }

    pub(crate) fn prepared_mask_generators(&self) -> Option<&[FixedGenerator]> {
        (!self.sparse_mask_generators.is_empty()).then_some(&self.sparse_mask_generators)
    }

    fn fixed_sparse_commitment(
        &self,
        coefficients: &[(usize, Fp)],
        blind: &Fp,
    ) -> Option<VestaProjective> {
        let mask = self.prepared_mask_generators()?;
        if coefficients.len() > K as usize + 1 {
            return None;
        }
        let mut tables = [self.prepared_blind_generator().table(); K as usize + 2];
        let mut scalars = [Fp::ZERO; K as usize + 2];
        scalars[0] = *blind;
        for (i, (index, scalar)) in coefficients.iter().enumerate() {
            tables[i + 1] = if *index == 0 {
                self.prepared_first_coefficient_generator.table()
            } else if index.is_power_of_two() {
                mask.get(index.trailing_zeros() as usize)?.table()
            } else {
                return None;
            };
            scalars[i + 1] = *scalar;
        }
        let len = coefficients.len() + 1;
        Some(FixedGenerator::sum_tables(&tables[..len], &scalars[..len]))
    }

    pub(crate) fn commit_coefficients(
        &self,
        coefficients: &SharedPoly,
        blind: &Fp,
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<VestaPoint, TargetError> {
        self.commit_coefficients_projective(coefficients, blind, workspace, execution)
            .map(|commitment| commitment.to_point())
    }

    pub(crate) fn commit_coefficients_projective(
        &self,
        coefficients: &SharedPoly,
        blind: &Fp,
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<VestaProjective, TargetError> {
        commit_dense(
            self.coefficient_bases(),
            self.prepared_blind_generator(),
            coefficients,
            blind,
            workspace,
            execution,
        )
    }

    pub(crate) fn commit_sparse_coefficients(
        &self,
        coefficients: &[(usize, Fp)],
        blind: &Fp,
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<VestaPoint, TargetError> {
        self.commit_sparse_coefficients_projective(coefficients, blind, workspace, execution)
            .map(|commitment| commitment.to_point())
    }

    pub(crate) fn commit_sparse_coefficients_projective(
        &self,
        coefficients: &[(usize, Fp)],
        blind: &Fp,
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<VestaProjective, TargetError> {
        if coefficients.is_empty()
            || coefficients
                .iter()
                .any(|(index, _)| *index >= self.srs.coefficient_generators.len())
            || coefficients.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        {
            return Err(TargetError::Dimension);
        }
        if let Some(point) = self.fixed_sparse_commitment(coefficients, blind) {
            return Ok(point);
        }
        let indices = coefficients
            .iter()
            .map(|(index, _)| *index as u32)
            .collect::<Vec<_>>();
        let scalars = coefficients
            .iter()
            .map(|(_, coefficient)| *coefficient)
            .collect::<Vec<_>>();
        let input = udon::msm::Input::indexed(self.coefficient_bases(), &indices, &scalars)
            .map_err(|_| TargetError::Dimension)?;
        let mut output = [VestaProjective::IDENTITY];
        workspace
            .prepare(&[input], execution.budget)
            .map_err(|_| TargetError::Dimension)?
            .execute(&mut output, &execution)
            .map_err(|_| TargetError::Dimension)?;
        let polynomial = output[0];
        Ok(polynomial.add(&self.prepared_blind_generator().mul(blind)))
    }

    #[cfg(test)]
    pub(crate) fn commit_lagrange_projective(
        &self,
        evaluations: &[Fp],
        blind: &Fp,
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<VestaProjective, TargetError> {
        commit_projective(
            &self.srs.lagrange_generators,
            self.prepared_blind_generator(),
            evaluations,
            blind,
            workspace,
            execution,
        )
    }

    /// Commits a batch of dense Lagrange-basis polynomials as one task
    /// group: the reference the fold-aware advice batch is checked against.
    #[cfg(test)]
    pub(crate) fn commit_lagrange_batch_projective(
        &self,
        jobs: &[(&SharedPoly, &Fp)],
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<Vec<VestaProjective>, TargetError> {
        commit_dense_batch(
            &self.srs.lagrange_generators,
            self.prepared_blind_generator(),
            jobs,
            workspace,
            execution,
        )
    }

    /// The absolute rows of the variable-base gadget's repeated coordinate
    /// run, the rows [`Self::commit_advice_batch_projective`] folds.
    pub(crate) fn repeated_coordinate_rows(&self) -> core::ops::Range<usize> {
        variable_base_mul::coordinate_rows()
    }

    /// The structured carve-outs of advice column `column`, each removing
    /// cells from the dense MSM and contributing them another way: the
    /// repeated variable-base coordinates, running sums transposed onto word
    /// or bit bases, constant-cell offsets, and selected fixed-window points.
    /// A column may carry several; they cover disjoint cells by construction
    /// (checked at load).
    fn prepare_advice_column_carveouts(&self, column: usize) -> Vec<Carveout> {
        let mut carveouts = Vec::with_capacity(4 + self.window_selections.len());
        if variable_base_mul::COORDINATE_COLUMNS.contains(&column) {
            carveouts.push(Carveout::FoldedRun);
        }
        if let Some(index) = self
            .word_bases
            .iter()
            .position(|bases| bases.column == column)
        {
            carveouts.push(Carveout::Words(index));
        }
        if let Some(index) = self
            .bit_bases
            .iter()
            .position(|bases| bases.column == column)
        {
            carveouts.push(Carveout::Bits(index));
        }
        if let Some(index) = self
            .constant_columns
            .iter()
            .position(|constants| constants.column == column)
        {
            carveouts.push(Carveout::Constants(index));
        }
        for (index, selection) in self.window_selections.iter().enumerate() {
            if selection.column == column && !selection.windows.is_empty() {
                carveouts.push(Carveout::Window(index));
            }
        }
        carveouts
    }

    /// The columns whose commitments transpose running sums onto word bases,
    /// in preparation order (the Sinsemilla columns, then the fixed-base
    /// running-sum column).
    #[cfg(test)]
    pub(crate) fn word_columns(&self) -> Vec<usize> {
        self.word_bases.iter().map(|bases| bases.column).collect()
    }

    /// The constant-cell columns as `(column, cell count)`.
    #[cfg(test)]
    pub(crate) fn constant_columns(&self) -> Vec<(usize, usize)> {
        self.constant_columns
            .iter()
            .map(|constants| (constants.column, constants.cells.len()))
            .collect()
    }

    /// How many of advice column `index`'s constant cells do not hold their
    /// constant (zero on every writer-produced column).
    #[cfg(test)]
    pub(crate) fn constant_mismatches(&self, index: usize, column: &[Fp]) -> usize {
        self.constant_columns
            .iter()
            .filter(|constants| constants.column == index)
            .flat_map(|constants| constants.cells.iter())
            .filter(|(row, constant)| (column[*row]).reduce() != (constant).reduce())
            .count()
    }

    /// The columns whose commitments transpose binary running-sum chains.
    #[cfg(test)]
    pub(crate) fn bit_columns(&self) -> Vec<usize> {
        self.bit_bases.iter().map(|bases| bases.column).collect()
    }

    /// How many of advice column `index`'s fixed-window coordinate cells the
    /// selection carve-out recognizes (every scheduled window on a
    /// writer-produced column); zero for a column without a selection.
    #[cfg(test)]
    pub(crate) fn window_selection_count(&self, index: usize, column: &[Fp]) -> usize {
        self.window_selections
            .iter()
            .filter(|selection| selection.column == index)
            .map(|selection| selection.select(column).len())
            .sum()
    }

    /// Commits the advice columns of a batch as one task group: each job is
    /// `(dense column, blind, advice column index)`, and the column index
    /// selects the column's prepared carve-outs.
    ///
    /// - A **folded run** (checked here: one run of equal cells `v` on
    ///   [`Self::repeated_coordinate_rows`]) commits as the single
    ///   table-driven term `v·H` over the prepared summed generators.
    /// - **Sinsemilla words**: every scheduled running-sum cell is replaced
    ///   by one MSM of the cells' ten-bit words and per-piece remainders over
    ///   the weighted word bases — exact for any cell values, cheap when the
    ///   words are small (two or three bucket additions per word instead of
    ///   a full-width scalar's thirty-odd).
    /// - **Window `x`**: each fixed-base window's `x` cell equal to one of
    ///   its eight table entries is replaced by the precomputed point for
    ///   that entry; the selected points are summed by a side task of the
    ///   batch. A cell matching no entry stays in the dense MSM.
    /// - **Equal residual scalars**: sum their Lagrange bases, then commit
    ///   once per distinct nonzero scalar. Singleton groups keep their
    ///   prepared bases; only combined bases need batch normalization.
    ///
    /// The carved-out cells are zeroed in a batch-lifetime copy; the callers'
    /// dense columns are untouched. The per-column preparation (copies, run
    /// checks, word extraction, selection, grouping) runs as pool tasks so none of it
    /// sits serially ahead of the batch. Output order is job order.
    pub(crate) fn commit_advice_batch_projective(
        &self,
        jobs: &[(&SharedPoly, &Fp, usize)],
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<Vec<VestaProjective>, TargetError> {
        if self.srs.lagrange_generators.len() != N
            || jobs.iter().any(|(column, _, _)| column.len() != N)
        {
            return Err(TargetError::Dimension);
        }
        let items = jobs
            .iter()
            .map(|(column, _, index)| (*column, *index))
            .collect::<Vec<_>>();
        let mut prepared = execution
            .map(items, |(column, index), execution| {
                let PreparedColumn {
                    scalars,
                    extras,
                    selection,
                    offset,
                } = self.prepare_advice_column(column, index, execution)?;
                let grouped = self.residual_copies.group(
                    &self.srs.lagrange_generators,
                    scalars.as_ref(),
                    index,
                );
                Ok((
                    Some(PreparedColumn {
                        scalars: grouped.scalars,
                        extras,
                        selection,
                        offset,
                    }),
                    grouped.bases,
                ))
            })
            .into_iter()
            .collect::<Result<Vec<_>, TargetError>>()?;

        let extra_capacity = prepared
            .iter()
            .map(|(column, _)| column.as_ref().expect("prepared column").extras.len())
            .sum::<usize>();
        let mut extra_jobs = Vec::with_capacity(extra_capacity);
        let mut side_jobs = Vec::with_capacity(jobs.len());
        let mut msm_jobs = Vec::with_capacity(2 * jobs.len() + extra_capacity);
        let mut shapes = Vec::with_capacity(jobs.len());
        for (prepared, bases) in &mut prepared {
            let PreparedColumn {
                scalars,
                extras,
                selection,
                offset,
            } = prepared.take().expect("prepared column consumed once");
            msm_jobs.push(CommitmentTerm::Dense {
                bases: Bases::Prepared(bases),
                scalars,
            });
            shapes.push((extras.len(), selection.is_some(), offset));
            extra_jobs.extend(extras);
            if let Some(selection) = selection {
                side_jobs.push(selection);
            }
        }
        let extra_count = extra_jobs.len();
        msm_jobs.extend(extra_jobs);
        msm_jobs.extend(jobs.iter().map(|(_, blind, _)| CommitmentTerm::Fixed {
            base: self.prepared_blind_generator(),
            scalar: **blind,
        }));
        // The callback itself always receives a serial sub-budget, even
        // when the outer scheduler can run several side jobs concurrently.
        let affine_side_sum = execution.budget == udon::exec::TaskBudget::SERIAL;
        let (mut outputs, side_results) =
            execute_with_side_jobs(workspace, execution, &msm_jobs, side_jobs, |item, _| {
                if affine_side_sum {
                    sum_selected_window_points_affine(item)
                } else {
                    sum_selected_window_points(item)
                }
            })
            .ok_or(TargetError::Dimension)?;
        if outputs.len() != 2 * jobs.len() + extra_count {
            return Err(TargetError::Dimension);
        }
        let (polynomials, remaining) = outputs.split_at_mut(jobs.len());
        let (extra_terms, blind_terms) = remaining.split_at(extra_count);
        let mut extras = extra_terms.iter();
        let mut side_results = side_results.into_iter();
        for ((polynomial, blind_term), (extra_count, has_selection, offset)) in
            polynomials.iter_mut().zip(blind_terms).zip(shapes)
        {
            let mut commitment = polynomial.add(blind_term);
            for _ in 0..extra_count {
                commitment = commitment.add(extras.next().ok_or(TargetError::Dimension)?);
            }
            if has_selection {
                commitment = commitment.add(&side_results.next().ok_or(TargetError::Dimension)?);
            }
            if let Some(offset) = offset {
                commitment = commitment.add(&offset);
            }
            *polynomial = commitment;
        }
        if extras.next().is_some() || side_results.next().is_some() {
            return Err(TargetError::Dimension);
        }
        outputs.truncate(jobs.len());
        Ok(outputs)
    }

    /// One advice column's staged scalars (the dense column, or its copy
    /// with every carved-out cell zeroed), its extra MSM jobs, and its
    /// selected window-`x` point indices, per its carve-outs.
    fn prepare_advice_column<'a>(
        &'a self,
        column: &'a SharedPoly,
        index: usize,
        execution: Execution<'_>,
    ) -> Result<PreparedColumn<'a, AdviceScalars<'a>>, TargetError> {
        if column.len() != N {
            return Err(TargetError::Dimension);
        }
        let carveouts = self
            .advice_carveouts
            .get(index)
            .map_or(&[][..], Vec::as_slice);
        if carveouts.is_empty() {
            return Ok(PreparedColumn {
                scalars: AdviceScalars::Borrowed(column),
                extras: Vec::with_capacity(0),
                selection: None,
                offset: None,
            });
        }
        let mut zeroed = execution.copy(column);
        let mut extras = Vec::with_capacity(carveouts.len());
        let mut selection = None;
        let mut offset = None;
        for &carveout in carveouts {
            match carveout {
                Carveout::FoldedRun => {
                    let rows = self.repeated_coordinate_rows();
                    let run = column.get(rows.clone()).ok_or(TargetError::Dimension)?;
                    let (value, rest) = run.split_first().ok_or(TargetError::Dimension)?;
                    if rest.iter().any(|cell| (cell).reduce() != (value).reduce()) {
                        return Err(TargetError::Malformed);
                    }
                    zeroed[rows].fill(<Fp>::ZERO);
                    extras.push(CommitmentTerm::Fixed {
                        base: &self.repeated_coordinate_base,
                        scalar: *value,
                    });
                }
                Carveout::Words(bases_index) => {
                    let bases = &self.word_bases[bases_index];
                    let mut words = execution.buffer(bases.bases.len(), false);
                    bases.write_words(column, &mut words)?;
                    for (rows, _) in &bases.pieces {
                        zeroed[rows.clone()].fill(<Fp>::ZERO);
                    }
                    extras.push(CommitmentTerm::Dense {
                        bases: Bases::Prepared(&bases.bases),
                        scalars: Column::new(words),
                    });
                }
                Carveout::Bits(bases_index) => {
                    let bases = &self.bit_bases[bases_index];
                    let mut scalars = execution.buffer(bases.bases.len(), false);
                    bases.write_scalars(column, &mut scalars)?;
                    for (rows, _) in &bases.chains {
                        for &row in rows {
                            zeroed[row] = <Fp>::ZERO;
                        }
                    }
                    extras.push(CommitmentTerm::Dense {
                        bases: Bases::Prepared(&bases.bases),
                        scalars: Column::new(scalars),
                    });
                }
                Carveout::Constants(constants_index) => {
                    let constants = &self.constant_columns[constants_index];
                    // The offset covers every constant cell; a cell that does
                    // not hold its constant stays dense and gets its
                    // constant subtracted back out, exactly.
                    let correction_count = constants
                        .cells
                        .iter()
                        .filter(|&&(row, constant)| (column[row]).reduce() != (constant).reduce())
                        .count();
                    let mut correction_rows = Vec::with_capacity(correction_count);
                    let mut correction_scalars = Vec::with_capacity(correction_count);
                    for &(row, constant) in &constants.cells {
                        if (column[row]).reduce() == (constant).reduce() {
                            zeroed[row] = <Fp>::ZERO;
                        } else {
                            correction_rows.push(row as u32);
                            correction_scalars.push(constant.neg());
                        }
                    }
                    if !correction_rows.is_empty() {
                        extras.push(CommitmentTerm::Indexed {
                            bases: self.lagrange_bases(),
                            indices: Column::new(correction_rows),
                            scalars: Column::new(correction_scalars),
                        });
                    }
                    offset = Some(constants.offset);
                }
                Carveout::Window(selection_index) => {
                    if selection.is_some() {
                        // One selected sum per column: the carve-outs are
                        // per coordinate column by construction.
                        return Err(TargetError::Malformed);
                    }
                    let window_selection = &self.window_selections[selection_index];
                    let mut selected = Vec::with_capacity(window_selection.windows.len());
                    for (row, base) in window_selection.selected(column) {
                        zeroed[row] = <Fp>::ZERO;
                        selected.push(base);
                    }
                    selection = Some((window_selection.bases, selected));
                }
            }
        }
        Ok(PreparedColumn {
            scalars: AdviceScalars::Owned(zeroed),
            extras,
            selection,
            offset,
        })
    }

    /// Commits a batch of Lagrange-basis polynomials whose columns are
    /// piecewise constant on the usable rows through the prepared prefix-sum
    /// intervals — one MSM term per run boundary plus the blinding tail — in
    /// one task group. A job falls back to the ordinary dense staged path
    /// when the prefix sums are unavailable.
    #[cfg(test)]
    pub(crate) fn commit_lagrange_mixed_batch_projective(
        &self,
        jobs: &[(LagrangeCommitScalars<'_>, &Fp)],
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<Vec<VestaProjective>, TargetError> {
        let msm_jobs = self.mixed_commit_jobs(jobs)?;
        let polynomials =
            execute_terms(workspace, execution, &msm_jobs).ok_or(TargetError::Dimension)?;
        combine_with_blind_terms(polynomials, jobs.len())
    }

    /// Commits a mixed batch of Lagrange-basis polynomials — interval jobs
    /// through the prefix sums, dense jobs through the staged path — while
    /// owned side jobs share the task group. Job order is output order, so
    /// callers publish in the order they submit.
    pub(crate) fn commit_lagrange_mixed_batch_projective_with_side_jobs<S, R, F>(
        &self,
        jobs: &[(LagrangeCommitScalars<'_>, &Fp)],
        side_jobs: Vec<S>,
        side_job: F,
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<(Vec<VestaProjective>, Vec<R>), TargetError>
    where
        S: Send,
        R: Send,
        F: Fn(S, Execution<'_>) -> R + Send + Sync,
    {
        let msm_jobs = self.mixed_commit_jobs(jobs)?;
        let (polynomials, side_results) =
            execute_with_side_jobs(workspace, execution, &msm_jobs, side_jobs, side_job)
                .ok_or(TargetError::Dimension)?;
        Ok((
            combine_with_blind_terms(polynomials, jobs.len())?,
            side_results,
        ))
    }

    /// Stages one MSM job per mixed commitment — an index-selected job over
    /// the prefix-sum table for an interval description, the dense staged
    /// path (through the prepared SRS table when configured) for a dense
    /// column — followed by one fixed-base job per blind, so every
    /// commitment's blind term rides the same task group.
    fn mixed_commit_jobs(
        &self,
        jobs: &[(LagrangeCommitScalars<'_>, &Fp)],
    ) -> Result<Vec<CommitmentTerm<'_>>, TargetError> {
        if self.srs.lagrange_generators.len() != N {
            return Err(TargetError::Dimension);
        }
        let interval_pairs = jobs
            .iter()
            .map(|(scalars, _)| {
                if scalars.dense().len() != N {
                    return Err(TargetError::Dimension);
                }
                match scalars {
                    LagrangeCommitScalars::PiecewiseConstantPrefix { runs, dense } => {
                        gather_interval_pairs(&self.lagrange_prefix_sums, runs, dense).map(Some)
                    }
                    LagrangeCommitScalars::Dense(_) => Ok(None),
                }
            })
            .collect::<Result<Vec<_>, TargetError>>()?;

        Ok(jobs
            .iter()
            .zip(interval_pairs)
            .map(|((scalars, _), pairs)| match pairs {
                Some((indices, deltas)) => CommitmentTerm::Indexed {
                    bases: Bases::Prepared(&self.lagrange_prefix_sums),
                    indices: Column::new(indices),
                    scalars: Column::new(deltas),
                },
                None => CommitmentTerm::Dense {
                    bases: self.lagrange_bases(),
                    scalars: scalars.dense().clone(),
                },
            })
            .chain(jobs.iter().map(|(_, blind)| CommitmentTerm::Fixed {
                base: self.prepared_blind_generator(),
                scalar: **blind,
            }))
            .collect())
    }

    /// Commits Lagrange-basis prefixes with one shared blinding contribution.
    pub(crate) fn commit_lagrange_prefix_batch_projective(
        &self,
        prefixes: &[impl AsRef<[Fp]>],
        blind: &Fp,
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<Vec<VestaProjective>, TargetError> {
        if prefixes
            .iter()
            .any(|scalars| scalars.as_ref().len() > self.srs.lagrange_generators.len())
        {
            return Err(TargetError::Dimension);
        }
        let msm_jobs = prefixes
            .iter()
            .map(|scalars| CommitmentTerm::BorrowedDense {
                bases: self.lagrange_bases().range(0..scalars.as_ref().len()),
                scalars: scalars.as_ref(),
            })
            .collect::<Vec<_>>();
        let mut polynomials =
            execute_terms(workspace, execution, &msm_jobs).ok_or(TargetError::Dimension)?;
        if polynomials.len() != prefixes.len() {
            return Err(TargetError::Dimension);
        }
        if !polynomials.is_empty() {
            let blind_term = if blind.is_one() {
                VestaProjective::from_affine(&PREPARED_POINTS.blind_generator)
            } else {
                self.prepared_blind_generator().mul(blind)
            };
            for polynomial in &mut polynomials {
                *polynomial = polynomial.add(&blind_term);
            }
        }
        Ok(polynomials)
    }

    /// Commits a batch of coefficient-basis polynomials as one task group.
    /// Builds the commitments independently of the produced-input pipeline.
    #[cfg(test)]
    pub(crate) fn commit_coefficients_batch_projective(
        &self,
        jobs: &[(&SharedPoly, &Fp)],
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<Vec<VestaProjective>, TargetError> {
        commit_dense_batch(
            &self.srs.coefficient_generators,
            self.prepared_blind_generator(),
            jobs,
            workspace,
            execution,
        )
    }

    /// Commits a batch of dense coefficient-basis polynomials and one
    /// sparse coefficient polynomial in the same task group. The sparse term is
    /// `Σ_k sparse_scalars[k] · G_{sparse_indices[k]} + sparse_blind · W`,
    /// index-selecting the coefficient generators in place (a small job runs
    /// as one whole task under the dense jobs' windows). Returns the dense
    /// commitments in job order and the sparse one.
    pub(crate) fn commit_coefficients_batch_with_sparse_projective(
        &self,
        jobs: &[(&SharedPoly, &Fp)],
        sparse_indices: Column<u32>,
        sparse_scalars: Arc<Vec<Fp>>,
        sparse_blind: &Fp,
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<(Vec<VestaProjective>, VestaProjective), TargetError> {
        let generators = &self.srs.coefficient_generators;
        if generators.len() != N
            || jobs.iter().any(|(scalars, _)| scalars.len() != N)
            || sparse_indices.is_empty()
            || sparse_indices.len() != sparse_scalars.len()
            || sparse_indices
                .iter()
                .any(|&index| index as usize >= generators.len())
        {
            return Err(TargetError::Dimension);
        }

        let mut msm_jobs = staged_commit_jobs(generators, self.prepared_blind_generator(), jobs, 2);
        msm_jobs.push(CommitmentTerm::Indexed {
            bases: Bases::Prepared(generators),
            indices: sparse_indices,
            scalars: Column::from(sparse_scalars),
        });
        msm_jobs.push(CommitmentTerm::Fixed {
            base: self.prepared_blind_generator(),
            scalar: *sparse_blind,
        });
        let mut outputs =
            execute_terms(workspace, execution, &msm_jobs).ok_or(TargetError::Dimension)?;
        let sparse_blind_term = outputs.pop().ok_or(TargetError::Dimension)?;
        let sparse_polynomial = outputs.pop().ok_or(TargetError::Dimension)?;
        let dense = combine_with_blind_terms(outputs, jobs.len())?;
        Ok((dense, sparse_polynomial.add(&sparse_blind_term)))
    }
}

/// Serial single-commitment oracle for the grouped paths.
#[cfg(test)]
fn commit_projective(
    generators: &[PreparedAffinePoint<Vesta>],
    blind_generator: &FixedGenerator,
    scalars: &[Fp],
    blind: &Fp,
    _workspace: &mut MsmWorkspace,
    _execution: Execution<'_>,
) -> Result<VestaProjective, TargetError> {
    if scalars.len() != N || generators.len() != N {
        return Err(TargetError::Dimension);
    }
    let polynomial = sum_prepared(generators, scalars).ok_or(TargetError::Dimension)?;
    Ok(polynomial.add(&blind_generator.mul(blind)))
}

fn commit_dense(
    generators: Bases<'_, Vesta>,

    blind_generator: &FixedGenerator,
    scalars: &SharedPoly,
    blind: &Fp,
    workspace: &mut MsmWorkspace,
    execution: Execution<'_>,
) -> Result<VestaProjective, TargetError> {
    if scalars.len() != N || generators.len() != N {
        return Err(TargetError::Dimension);
    }
    // The polynomial job and its blind term share one task group.
    let polynomial_job = CommitmentTerm::Dense {
        bases: generators,
        scalars: scalars.clone(),
    };
    let jobs = [
        polynomial_job,
        CommitmentTerm::Fixed {
            base: blind_generator,
            scalar: *blind,
        },
    ];
    let mut outputs = execute_terms(workspace, execution, &jobs).ok_or(TargetError::Dimension)?;
    let blind_term = outputs.pop().ok_or(TargetError::Dimension)?;
    let polynomial = outputs.pop().ok_or(TargetError::Dimension)?;
    Ok(polynomial.add(&blind_term))
}

/// One Lagrange-basis commitment job's scalars for the interval batch path.
///
/// # Support and blinding contract
///
/// - **Support.** The interval description covers exactly the usable prefix
///   `[0, USABLE_ROWS_END)`: `runs` are `(start row, value)` pairs with the
///   first start at row 0 and strictly increasing starts, each run extending
///   to the next start (the last to `USABLE_ROWS_END`). Disorder, a missing
///   row-0 run, or a start at or past `USABLE_ROWS_END` is rejected by the
///   gatherer; a duplicate start is disorder. Adjacent runs with equal
///   values are permitted (they cost one zero-scalar term) but not required
///   to be merged.
/// - **Blinding.** The tail rows `USABLE_ROWS_END..N` — every blinding cell —
///   are always committed densely against the tail generators from `dense`,
///   never through the runs, so no sparse path can drop a blinding
///   contribution; the commitment blind itself rides the batch's fixed-base
///   job. Structural support (which rows carry runs) is a property of the
///   circuit's fixed copy graph or table order, not of zeros observed in one
///   witness.
/// - **Dense form.** `dense` is the same full `N`-row column and is what the
///   job commits when the prefix-sum table is unavailable; every consumer
///   downstream of the commitment (transforms, evaluations) still needs it,
///   so the interval path removes MSM work, not the column.
pub(crate) enum LagrangeCommitScalars<'a> {
    /// A column that is piecewise constant on `[0, USABLE_ROWS_END)`,
    /// described by ascending `(start row, value)` runs. `dense` carries the
    /// same full column of length `N`: its blinding tail is committed
    /// densely, and it is the whole job's fallback when prefix sums are
    /// unavailable.
    PiecewiseConstantPrefix {
        runs: &'a [(u32, Fp)],
        dense: &'a SharedPoly,
    },
    /// A full `N`-row column with no interval structure to exploit: committed
    /// through the dense staged path. Lets a batch mix interval and dense
    /// jobs while keeping one job order for publication.
    Dense(&'a SharedPoly),
}

impl LagrangeCommitScalars<'_> {
    /// The full `N`-row column every variant carries.
    pub(crate) fn dense(&self) -> &SharedPoly {
        match self {
            Self::PiecewiseConstantPrefix { dense, .. } | Self::Dense(dense) => dense,
        }
    }
}

/// Builds the prepared Lagrange prefix sums `P[j] = Σ_{i<j} G_i` for `j` in
/// `1..=USABLE_ROWS_END` followed by the plain tail generators, or `None` if
/// any prefix is the identity. The embedded prefix-sum table stores exactly
/// this construction; tests recompute it here to validate the embedded data.
#[cfg(test)]
pub(super) fn prepare_lagrange_prefix_sums(points: &[VestaAffine]) -> Option<Vec<VestaAffine>> {
    if points.len() != N {
        return None;
    }
    let mut running = VestaProjective::IDENTITY;
    let mut prefixes = Vec::with_capacity(USABLE_ROWS_END);
    for point in &points[..USABLE_ROWS_END] {
        running = running.add_mixed(point);
        prefixes.push(running);
    }
    normalized(&prefixes)
        .iter()
        .map(|point| point.as_affine().copied())
        .chain(points[USABLE_ROWS_END..].iter().map(|point| Some(*point)))
        .collect()
}

/// Telescopes a piecewise-constant usable prefix into indices into the
/// combined prefix-sum table plus their scalars.
///
/// For runs `(a_k, c_k)` covering `[0, USABLE_ROWS_END)` the prefix commits
/// as `Σ_{k≥1} (c_{k-1} − c_k)·P[a_k] + c_last·P[USABLE_ROWS_END]` (the
/// `P[a_0] = P[0]` term is the empty sum), and the blinding tail rows commit
/// densely against the table's tail generators.
fn gather_interval_pairs(
    prefix_sums: &[PreparedAffinePoint<Vesta>],
    runs: &[(u32, Fp)],
    dense: &[Fp],
) -> Result<(Vec<u32>, Vec<Fp>), TargetError> {
    let Some(((first_start, _), rest)) = runs.split_first() else {
        return Err(TargetError::Dimension);
    };
    let (last_start, last_value) = runs.last().expect("runs are nonempty");
    if *first_start != 0
        || (*last_start as usize) >= USABLE_ROWS_END
        || runs.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        || prefix_sums.len() != N
    {
        return Err(TargetError::Dimension);
    }
    let tail = &dense[USABLE_ROWS_END..];
    let mut indices = Vec::with_capacity(runs.len() + tail.len());
    let mut scalars = Vec::with_capacity(runs.len() + tail.len());
    for ((_, previous_value), (start, value)) in runs.iter().zip(rest) {
        indices.push(*start - 1);
        scalars.push(previous_value.sub(value));
    }
    indices.push(USABLE_ROWS_END as u32 - 1);
    scalars.push(*last_value);
    indices.extend(USABLE_ROWS_END as u32..N as u32);
    scalars.extend_from_slice(tail);
    Ok((indices, scalars))
}

/// One structured carve-out of an advice column's commitment; see
/// `Parameters::prepare_advice_column_carveouts`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Carveout {
    FoldedRun,
    /// Index into `Parameters::word_bases`.
    Words(usize),
    /// Index into `Parameters::bit_bases`.
    Bits(usize),
    /// Index into `Parameters::constant_columns`.
    Constants(usize),
    /// Index into `Parameters::window_selections`.
    Window(usize),
}

/// One advice column staged for the batch: its scalars for the dense job,
/// extra MSM jobs, and the selected window-`x` point indices for a side task.
struct PreparedColumn<'a, S = SharedPoly> {
    scalars: S,
    extras: Vec<CommitmentTerm<'a>>,
    selection: Option<(&'static [VestaAffine], Vec<u32>)>,
    /// A precomputed point added to the commitment (the constant offset).
    offset: Option<VestaProjective>,
}

/// Residuals remain borrowed or uniquely owned until grouping consumes them.
enum AdviceScalars<'a> {
    Borrowed(&'a [Fp]),
    Owned(Buffer<Fp>),
}

impl AsRef<[Fp]> for AdviceScalars<'_> {
    fn as_ref(&self) -> &[Fp] {
        match self {
            Self::Borrowed(values) => values,
            Self::Owned(values) => values,
        }
    }
}

/// One column's writer-constant cells and their precomputed offset.
pub(crate) struct ConstantColumn {
    pub(super) column: usize,
    /// `(absolute row, the constant the writer assigns there)`.
    pub(super) cells: Vec<(usize, Fp)>,
    /// `Σ k·G_row` over `cells`.
    pub(super) offset: VestaProjective,
}

/// The fixed-base windows of one coordinate column with their selectable
/// values: window `i` (flat `FIXED_BASE_REGIONS` order) sits at `rows[i]` and
/// its eight table entries' points are `bases[8·i..8·i+8]`. Windows whose
/// region table is unavailable are omitted (their cells stay dense).
pub(super) struct WindowSelection {
    pub(super) column: usize,
    pub(super) bases: &'static [VestaAffine],
    pub(super) windows: Vec<(usize, [Fp; FIXED_BASE_WINDOW_SIZE as usize], u32)>,
}

impl WindowSelection {
    /// The `(row, flat base index)` of every window whose cell equals one of
    /// its table entries.
    #[cfg(test)]
    pub(super) fn select(&self, column: &[Fp]) -> Vec<(usize, u32)> {
        self.selected(column).collect()
    }

    fn selected<'a>(&'a self, column: &'a [Fp]) -> impl Iterator<Item = (usize, u32)> + 'a {
        self.windows.iter().filter_map(|(row, values, first_base)| {
            let cell = column.get(*row)?;
            values
                .iter()
                .position(|value| value.reduce() == cell.reduce())
                .map(|digit| (*row, first_base + digit as u32))
        })
    }
}

/// Sums selected window points using one fresh affine/field scratch pair.
fn sum_selected_window_points_affine(
    (bases, selection): (&'static [VestaAffine], Vec<u32>),
) -> VestaProjective {
    let mut points = Vec::with_capacity(selection.len());
    for index in selection {
        points.push(bases[index as usize]);
    }
    let mut fields = alloc::vec![udon::field::Fq::ZERO; points.len()];
    let result = VestaAffine::sum_in_place(&mut points, &mut fields);
    drop(fields);
    drop(points);
    result
}

/// Sums the selected window points of one column (a batch side task).
fn sum_selected_window_points(
    (bases, selection): (&'static [VestaAffine], Vec<u32>),
) -> VestaProjective {
    let mut sum = VestaProjective::IDENTITY;
    for index in selection {
        sum = sum.add_mixed(&bases[index as usize]);
    }
    sum
}

/// The chain bases of one column of the variable-base gadget: for every
/// chain in footprint order, its initial-sum base `K` followed by its bit
/// bases `H_1..H_m`, prepared as MSM bases.
pub(crate) struct BitColumnBases {
    pub(super) column: usize,
    pub(super) bases: Vec<PreparedAffinePoint<Vesta>>,
    /// `(absolute rows `r_0..r_m` of the chain, index of its first base)`.
    pub(super) chains: Vec<(Vec<usize>, usize)>,
}

impl BitColumnBases {
    /// The column's chain scalars in base order: for each chain, `z_0` then
    /// `b_k = z_k − 2·z_{k−1}` for `k = 1..=m`. Exact for any cell values.
    fn write_scalars(&self, column: &[Fp], scalars: &mut [Fp]) -> Result<(), TargetError> {
        if scalars.len() != self.bases.len() {
            return Err(TargetError::Dimension);
        }
        let mut output = scalars.iter_mut();
        for (rows, _) in &self.chains {
            let mut previous: Option<Fp> = None;
            for &row in rows {
                let cell = *column.get(row).ok_or(TargetError::Dimension)?;
                *output.next().ok_or(TargetError::Dimension)? = match previous {
                    None => cell,
                    Some(previous) => cell.sub(&previous.double()),
                };
                previous = Some(cell);
            }
        }
        if output.next().is_some() {
            return Err(TargetError::Dimension);
        }
        Ok(())
    }
}

/// The weighted word bases of one running-sum column: for every scheduled
/// piece in schedule order, its `m` word bases `H_0..H_{m-1}` followed by its
/// remainder base `B·H_{m-1}`, prepared as MSM bases (a property of the SRS
/// and the layout, shared by every Action and proof for the process).
pub(crate) struct WordColumnBases {
    pub(super) column: usize,
    /// Bits per word: the radix `B = 2^word_bits` of the column's streams.
    pub(super) word_bits: usize,
    pub(super) bases: Vec<PreparedAffinePoint<Vesta>>,
    /// `(absolute rows of the piece's running sums, index of its first base)`.
    pub(super) pieces: Vec<(core::ops::Range<usize>, usize)>,
}

impl WordColumnBases {
    /// The column's word scalars in base order: for each piece, the words
    /// `d_j = z_j − B·z_{j+1}` for `j < m − 1`, then the last cell's low
    /// `WORD_BITS` bits and its remainder `t = z_{m-1} >> WORD_BITS` (so that
    /// `z_{m-1} = d_{m-1} + B·t` exactly). Exact for any cell values.
    fn write_words(&self, column: &[Fp], words: &mut [Fp]) -> Result<(), TargetError> {
        if words.len() != self.bases.len() {
            return Err(TargetError::Dimension);
        }
        let radix = <Fp>::from_u64(1 << self.word_bits);
        let mut output = words.iter_mut();
        for (rows, _) in &self.pieces {
            let cells = column.get(rows.clone()).ok_or(TargetError::Dimension)?;
            let last = cells.last().ok_or(TargetError::Dimension)?;
            for pair in cells.windows(2) {
                *output.next().ok_or(TargetError::Dimension)? = pair[0].sub(&pair[1].mul(&radix));
            }
            let last = last.to_canonical_uint();
            let low = last
                .window(0, self.word_bits)
                .ok_or(TargetError::Dimension)?;
            *output.next().ok_or(TargetError::Dimension)? = <Fp>::from_u64(low);
            *output.next().ok_or(TargetError::Dimension)? =
                <Fp>::from_canonical_uint(last.shr(self.word_bits))
                    .ok_or(TargetError::Dimension)?;
        }
        if output.next().is_some() {
            return Err(TargetError::Dimension);
        }
        Ok(())
    }
}

#[cfg(test)]
fn commit_dense_batch(
    generators: &[PreparedAffinePoint<Vesta>],

    blind_generator: &FixedGenerator,
    jobs: &[(&SharedPoly, &Fp)],
    workspace: &mut MsmWorkspace,
    execution: Execution<'_>,
) -> Result<Vec<VestaProjective>, TargetError> {
    if generators.len() != N || jobs.iter().any(|(scalars, _)| scalars.len() != N) {
        return Err(TargetError::Dimension);
    }
    let msm_jobs = staged_commit_jobs(generators, blind_generator, jobs, 0);
    let polynomials =
        execute_terms(workspace, execution, &msm_jobs).ok_or(TargetError::Dimension)?;
    combine_with_blind_terms(polynomials, jobs.len())
}

/// Stages one MSM job per polynomial — through the prepared SRS table when
/// one is configured — followed by one fixed-base job per blind, so every
/// commitment's blind term rides the same task group. The buffer reserves
/// `extra` further slots for jobs the caller appends.
fn staged_commit_jobs<'a>(
    generators: &'a [PreparedAffinePoint<Vesta>],

    blind_generator: &'a FixedGenerator,
    jobs: &[(&SharedPoly, &Fp)],
    extra: usize,
) -> Vec<CommitmentTerm<'a>> {
    let mut staged = Vec::with_capacity(2 * jobs.len() + extra);
    staged.extend(
        jobs.iter()
            .map(|(scalars, _)| CommitmentTerm::Dense {
                bases: Bases::Prepared(generators),
                scalars: (*scalars).clone(),
            })
            .chain(jobs.iter().map(|(_, blind)| CommitmentTerm::Fixed {
                base: blind_generator,
                scalar: **blind,
            })),
    );
    staged
}

/// Combines a grouped scheduler's polynomial and blind halves in place.
fn combine_with_blind_terms(
    mut outputs: Vec<VestaProjective>,
    job_count: usize,
) -> Result<Vec<VestaProjective>, TargetError> {
    if outputs.len() != 2 * job_count {
        return Err(TargetError::Dimension);
    }
    let (polynomials, blind_terms) = outputs.split_at_mut(job_count);
    for (polynomial, blind_term) in polynomials.iter_mut().zip(blind_terms) {
        *polynomial = polynomial.add(blind_term);
    }
    outputs.truncate(job_count);
    Ok(outputs)
}
