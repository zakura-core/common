//! Resolve borrowed Action views and fold residue windows into degree classes.

use super::*;

/// Compile the pinned frame slots while retaining the gathered buffers' runtime
/// row and fixed stride. Every slot copies its field value without arithmetic.
mod frame_gather {
    use super::{ADVICE_COLUMNS, Fp, GATHER_WIDTH};
    use sensei_shared::queries::{
        ADVICE_QUERIES, FIXED_QUERIES, GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, INSTANCE_QUERIES,
        QueryKind,
    };

    const fn resolve_slot(slot: usize) -> (QueryKind, usize, usize) {
        let (kind, query_index) = GATE_QUERY_DESCRIPTORS[slot];
        let query = match kind {
            QueryKind::Advice => ADVICE_QUERIES[query_index],
            QueryKind::Fixed => FIXED_QUERIES[query_index],
            QueryKind::Instance => INSTANCE_QUERIES[query_index],
        };
        let halo_row = match query.rotation {
            -1 => 0,
            0 => 1,
            1 => 2,
            _ => panic!("unsupported frame rotation"),
        };
        match kind {
            QueryKind::Fixed => assert!(query.rotation == 0),
            QueryKind::Instance => assert!(query.column == 0 && query.rotation == 0),
            QueryKind::Advice => assert!(query.column < ADVICE_COLUMNS),
        }
        (kind, query.column, halo_row)
    }

    #[inline(always)]
    fn gather_slot<const SLOT: usize>(
        block: &[Fp],
        fixed_block: &[Fp],
        fixed_stride: usize,
        r: usize,
    ) -> Fp {
        let (kind, column, halo_row) = const { resolve_slot(SLOT) };
        match kind {
            QueryKind::Advice => block[(r + halo_row) * GATHER_WIDTH + column],
            QueryKind::Fixed => fixed_block[r * fixed_stride + column],
            QueryKind::Instance => block[(r + 1) * GATHER_WIDTH + ADVICE_COLUMNS],
        }
    }

    #[inline(always)]
    pub(super) fn fill_frame(
        frame: &mut [Fp; GATE_QUERY_COUNT],
        block: &[Fp],
        fixed_block: &[Fp],
        fixed_stride: usize,
        r: usize,
    ) {
        macro_rules! fill_slots {
            ($($slot:literal),+ $(,)?) => {
                $(frame[$slot] = gather_slot::<$slot>(block, fixed_block, fixed_stride, r);)+
            };
        }
        const {
            assert!(GATE_QUERY_COUNT == 49);
        }
        fill_slots![
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
            46, 47, 48,
        ];
    }

    // ActionPlan remains the runtime validation boundary. Check that its halo
    // offsets agree with the pinned shape without retaining another per-action copy.
    pub(super) const ROTATIONS: [usize; GATE_QUERY_COUNT] = {
        let mut rotations = [0; GATE_QUERY_COUNT];
        let mut slot = 0;
        while slot < GATE_QUERY_COUNT {
            rotations[slot] = resolve_slot(slot).2;
            slot += 1;
        }
        rotations
    };

    #[cfg(test)]
    mod tests {
        use super::super::FRAME_GROUP_ROWS;
        use super::*;

        // Pin the actual column/rotation mapping independently of the resolver and
        // of query-table indices. In particular fixed query 0 means column 3.
        const ADVICE_SLOTS: [(usize, isize); 25] = [
            (0, 0),
            (1, 0),
            (2, 0),
            (3, 0),
            (4, 0),
            (5, 0),
            (6, 0),
            (7, 0),
            (8, 0),
            (9, 0),
            (9, 1),
            (9, -1),
            (2, 1),
            (3, 1),
            (4, 1),
            (5, 1),
            (0, 1),
            (1, 1),
            (7, 1),
            (8, 1),
            (6, -1),
            (1, -1),
            (6, 1),
            (7, -1),
            (8, -1),
        ];
        const FIXED_SLOTS: [usize; 24] = [
            3, 11, 4, 5, 6, 7, 8, 9, 10, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
        ];

        fn tagged(tag: u64) -> Fp {
            // Distinct full-width loose values: a copy must preserve all four raw
            // Montgomery limbs, including values above the canonical modulus.
            Fp::from_montgomery_limbs([
                u64::MAX ^ tag,
                tag.rotate_left(29),
                0xa5a5_5a5a_f0f0_0f0f ^ tag.rotate_left(47),
                0x7fff_ffff_ffff_ffff - tag,
            ])
        }

        #[test]
        fn full_frame_gather_preserves_mapping_halos_and_raw_limbs() {
            assert_eq!(GATE_QUERY_COUNT, ADVICE_SLOTS.len() + FIXED_SLOTS.len());
            assert_eq!(GATHER_WIDTH, 25);
            assert_eq!(FRAME_GROUP_ROWS, 4);
            for (slot, &(column, rotation)) in ADVICE_SLOTS.iter().enumerate() {
                let (kind, query_index) = GATE_QUERY_DESCRIPTORS[slot];
                assert_eq!(kind, QueryKind::Advice);
                let query = ADVICE_QUERIES[query_index];
                assert_eq!((query.column, query.rotation as isize), (column, rotation));
                assert_eq!(ROTATIONS[slot], (rotation + 1) as usize);
            }
            for (i, &column) in FIXED_SLOTS.iter().enumerate() {
                let slot = ADVICE_SLOTS.len() + i;
                let (kind, query_index) = GATE_QUERY_DESCRIPTORS[slot];
                assert_eq!(kind, QueryKind::Fixed);
                let query = FIXED_QUERIES[query_index];
                assert_eq!((query.column, query.rotation), (column, 0));
                assert_eq!(ROTATIONS[slot], 1);
            }

            // Short final tiles use their own following halo, not the fourth row's
            // halo. Extra fixed columns also catch accidental compile-time strides.
            for group_len in 1..=FRAME_GROUP_ROWS {
                let block: Vec<_> = (0..(group_len + 2) * GATHER_WIDTH)
                    .map(|index| tagged(0x10000 + index as u64))
                    .collect();
                for fixed_stride in [
                    sensei_shared::dimensions::FIXED_COLUMNS,
                    sensei_shared::dimensions::FIXED_COLUMNS + 3,
                ] {
                    let fixed: Vec<_> = (0..group_len * fixed_stride)
                        .map(|index| tagged(0x20000 + index as u64))
                        .collect();
                    for row in 0..group_len {
                        let guard = tagged(0x30000);
                        let mut output = [guard; GATE_QUERY_COUNT + 2];
                        fill_frame(
                            (&mut output[1..=GATE_QUERY_COUNT]).try_into().unwrap(),
                            &block,
                            &fixed,
                            fixed_stride,
                            row,
                        );
                        assert_eq!(output[0].montgomery_limbs(), guard.montgomery_limbs());
                        assert_eq!(
                            output[GATE_QUERY_COUNT + 1].montgomery_limbs(),
                            guard.montgomery_limbs()
                        );
                        for (slot, &(column, rotation)) in ADVICE_SLOTS.iter().enumerate() {
                            let halo_row = (row as isize + 1 + rotation) as usize;
                            let expected = &block[halo_row * GATHER_WIDTH + column];
                            assert_eq!(
                                output[slot + 1].montgomery_limbs(),
                                expected.montgomery_limbs(),
                                "advice slot={slot} row={row} tile={group_len} stride={fixed_stride}"
                            );
                        }
                        for (i, &column) in FIXED_SLOTS.iter().enumerate() {
                            let slot = ADVICE_SLOTS.len() + i;
                            let expected = &fixed[row * fixed_stride + column];
                            assert_eq!(
                                output[slot + 1].montgomery_limbs(),
                                expected.montgomery_limbs(),
                                "fixed slot={slot} row={row} tile={group_len} stride={fixed_stride}"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// Prepared per-action inputs for the fused classed quotient fold: the gate
/// query frame sources, the kept full-width permutation chunks, the
/// singleton chunk's data, and the absolute y-powers owed to every slot
/// carved out of the 8N accumulator. Every coset is a
/// borrowed tile view, resolved once per row task.
struct QuotientFoldAction<'a> {
    /// The Action's advice cosets by column, read by the lookup input kernels.
    advice_columns: [FpCosetView<'a>; ADVICE_COLUMNS],
    instance_column: FpCosetView<'a>,
    query_sources: [FoldColumnSource; GATE_QUERY_COUNT],
    kept_sets: [KeptPermutationSet<'a>; KEPT_PERMUTATION_SETS],
    /// The action's kept (full-width) permutation grand-product cosets.
    kept_products: [FpCosetView<'a>; KEPT_PERMUTATION_SETS],
    /// The singleton permutation set's grand product on the 2N class coset,
    /// read at extended rows `≡ 0 (mod 4)` and their `+8` rotation.
    singleton_product: FpClass2NView<'a>,
    /// The action's lookup grand-product cosets, one per lookup.
    lookup_products: [FpCosetView<'a>; fold_order::LOOKUP_COUNT],
    lookup_cosets: [LookupCosetViews<'a>; fold_order::LOOKUP_COUNT],
    set_2_values: FpCosetView<'a>,
    set_2_sigma: FpCosetView<'a>,
    set_2_beta_delta: Fp,
    gate_powers_2n: &'a [Fp; generated_expressions::GATE_PROGRAMS_2N.len()],
    gate_curve_powers_4n: &'a [Fp; 2],
    perm_l_0_power: Fp,
    perm_l_last_power: Fp,
    continuity_powers: &'a [Fp],
    set_2_rule_power: Fp,
    lookup_l_0_powers: &'a [Fp],
    lookup_l_last_powers: &'a [Fp],
    lookup_permuted_l_0_powers: &'a [Fp],
    lookup_continuity_powers: &'a [Fp],
}

/// A column view into an advice or fixed gather, reused by lookup kernels.
struct GatheredColumn<'a, const STRIDE: usize> {
    block: &'a [Fp],
    column: usize,
}
impl<const STRIDE: usize> core::ops::Index<usize> for GatheredColumn<'_, STRIDE> {
    type Output = Fp;
    fn index(&self, row: usize) -> &Fp {
        &self.block[row * STRIDE + self.column]
    }
}

/// Scratch retained through the six family passes over one Action's tile.
struct FoldTile {
    columns: crate::native::buffer::Buffer<Fp>,
    carried: [Fp; 2],
    frames: crate::native::buffer::Buffer<Fp>,
    cubics: [SinsemillaCubics; FRAME_GROUP_ROWS],
    curve_relations: [Fp; FRAME_GROUP_ROWS],
    sums: [generated_expressions::RowSum; FRAME_GROUP_ROWS],
}

/// Action views a row task holds inline before spilling into a vector.
const INLINE_FOLD_ACTIONS: usize = 16;

/// A row task's resolved [`QuotientFoldAction`] views, in Action order.
struct FoldActionViews<'a> {
    inline: [Option<QuotientFoldAction<'a>>; INLINE_FOLD_ACTIONS],
    spilled: Vec<QuotientFoldAction<'a>>,
}

impl<'a> FoldActionViews<'a> {
    fn iter(&self) -> impl Iterator<Item = &QuotientFoldAction<'a>> {
        self.inline.iter().flatten().chain(&self.spilled)
    }

    fn len(&self) -> usize {
        self.inline.iter().flatten().count() + self.spilled.len()
    }

    fn first(&self) -> Option<&QuotientFoldAction<'a>> {
        self.iter().next()
    }
}

/// One kept (full-width) permutation chunk's fold inputs: its grand-product
/// coset and the per-column gather sources, sigma slices, and `β·δⁱ` weights.
struct KeptPermutationSet<'a> {
    product: FpCosetView<'a>,
    column_sources: [FoldColumnSource; PERMUTATION_CHUNK_LEN],
    sigma_columns: &'a [FpCosetView<'a>],
    beta_deltas: &'a [Fp],
}

/// One Action's lookup cosets as a row task reads them.
#[derive(Clone, Copy)]
struct LookupCosetViews<'a> {
    compressed_table: FpCosetView<'a>,
    permuted_input: FpCosetView<'a>,
    permuted_table: FpCosetView<'a>,
}

impl FoldPlan<'_> {
    /// Resolves the per-action fold views from the plans built once per
    /// proof: slice lookups by stored source, borrowed powers, no validation,
    /// and no allocation for up to [`INLINE_FOLD_ACTIONS`] Actions.
    fn actions(&self) -> FoldActionViews<'_> {
        let plans = &self.action_plans;
        FoldActionViews {
            inline: core::array::from_fn(|index| {
                plans.get(index).map(|plan| self.action_view(index, plan))
            }),
            spilled: plans
                .iter()
                .enumerate()
                .skip(INLINE_FOLD_ACTIONS)
                .map(|(index, plan)| self.action_view(index, plan))
                .collect(),
        }
    }

    fn action_view<'a>(
        &'a self,
        action_index: usize,
        plan: &'a ActionPlan,
    ) -> QuotientFoldAction<'a> {
        debug_assert_eq!(plan.query_rotations, frame_gather::ROTATIONS);
        let inputs = &self.inputs;
        let fixed_views = inputs.fixed_cosets.as_slice();
        let sigma_cosets = inputs.sigma_cosets.as_slice();
        let beta_deltas = inputs.beta_deltas.as_slice();
        let advice = inputs.advice_cosets[action_index].as_slice();
        let instance = inputs.instance_cosets[action_index].view();
        let resolve = |source: FoldColumnSource| -> FpCosetView<'a> {
            match source {
                FoldColumnSource::Fixed(column) => fixed_views[column],
                FoldColumnSource::Advice(column) => advice[column].view(),
                FoldColumnSource::Instance => instance,
            }
        };
        let products = &inputs.permutation_cosets[action_index];
        let kept_products: [FpCosetView<'a>; KEPT_PERMUTATION_SETS] =
            core::array::from_fn(|set| products.kept[set].view());
        let kept_sets = plan.kept_sets.map(|set| KeptPermutationSet {
            product: kept_products[set.set_index],
            column_sources: set.columns,
            sigma_columns: &sigma_cosets
                [set.first_column..set.first_column + PERMUTATION_CHUNK_LEN],
            beta_deltas: &beta_deltas[set.first_column..set.first_column + PERMUTATION_CHUNK_LEN],
        });
        let lookup_cosets = inputs.lookup_cosets[action_index].as_slice();
        QuotientFoldAction {
            advice_columns: core::array::from_fn(|column| advice[column].view()),
            instance_column: instance,
            query_sources: plan.query_sources,
            kept_sets,
            kept_products,
            singleton_product: products.singleton.view(),
            lookup_products: core::array::from_fn(|lookup| {
                inputs.lookup_product_cosets[action_index][lookup].view()
            }),
            lookup_cosets: core::array::from_fn(|lookup| {
                let cosets = &lookup_cosets[lookup];
                LookupCosetViews {
                    compressed_table: cosets.compressed_table.view(),
                    permuted_input: cosets.permuted_input.view(),
                    permuted_table: cosets.permuted_table.view(),
                }
            }),
            set_2_values: resolve(plan.set_2_source),
            set_2_sigma: self.constants.set_2_sigma,
            set_2_beta_delta: self.constants.set_2_beta_delta,
            gate_powers_2n: &plan.gate_powers_2n,
            gate_curve_powers_4n: &plan.gate_curve_powers_4n,
            perm_l_0_power: plan.perm_l_0_power,
            perm_l_last_power: plan.perm_l_last_power,
            continuity_powers: &plan.continuity_powers,
            set_2_rule_power: plan.set_2_rule_power,
            lookup_l_0_powers: &plan.lookup_l_0_powers,
            lookup_l_last_powers: &plan.lookup_l_last_powers,
            lookup_permuted_l_0_powers: &plan.lookup_permuted_l_0_powers,
            lookup_continuity_powers: &plan.lookup_continuity_powers,
        }
    }

    /// Folds one residue-major window into the four quotient classes and a
    /// separate 4N lookup branch. Smaller chunks are empty off their class.
    pub(super) fn fold_rows(
        &self,
        execution: crate::native::worker::Execution<'_>,
        window: FoldWindow,
        chunks: [&mut [Fp]; 5],
    ) -> Result<(), Error> {
        let [chunk_8n, chunk_4n, chunk_2n, chunk_n, chunk_lookup] = chunks;
        let actions = self.actions();
        let target = self.target;
        let constants = &self.constants;
        let (beta, gamma) = (&self.inputs.beta, &self.inputs.gamma);
        let l_0 = target.boundaries().l_0();
        let l_last = target.boundaries().l_last();
        let active_rows = target.boundaries().active_rows();
        let coset_generator = target.domain().coset_generator();
        let extended_omega = target.domain().extended_omega();
        let gate_selectors = target.gate_selectors();
        let y_powers = &constants.y_powers;
        // With several Actions, the affine gate bodies are folded once per
        // row on the challenge-weighted aggregated frame; alone, the complete
        // single-Action kernel runs unchanged.
        let action_count = actions.len();
        let shared_affine = action_count > 1;
        if constants.action_weights.len() != action_count {
            return Err(Error::InternalInvariant);
        }
        let slot_powers = &constants.slot_powers;
        let rule_powers = &constants.rule_powers;
        let lookup_rule_powers = &constants.lookup_rule_powers;
        let y_action_step = &constants.y_action_step;
        let (scale_8n, scale_4n, scale_2n, scale_n) = (
            &constants.scale_8n,
            &constants.scale_4n,
            &constants.scale_2n,
            &constants.scale_n,
        );
        let fixed_cosets = self.inputs.fixed_cosets.as_slice();
        // The permutation rules' fixed factors — `β·σ_k(X) + γ` on the left
        // and `β·δ_k·X + γ` on the right — depend only on the row, so they
        // are formed once per row and shared by every Action's kept sets
        // (the sets' σ columns and β·δ weights are target-wide).
        let fixed_sets = actions
            .first()
            .map(|action| action.kept_sets.as_slice())
            .unwrap_or(&[]);
        // One entry per kept-set column — the fixed `FIXED_FACTOR_COLUMNS`
        // shape — so plain arrays, not per-task vectors.
        let mut left_offsets = [<Fp>::ZERO; FIXED_FACTOR_COLUMNS];
        let mut right_offsets = [<Fp>::ZERO; FIXED_FACTOR_COLUMNS];
        let set_2 = actions
            .first()
            .map(|action| (action.set_2_sigma, action.set_2_beta_delta));
        // Which classes this window's rows fold on is fixed by its residue.
        let fold_4n = window.residue.is_multiple_of(2);
        let fold_2n = window.residue.is_multiple_of(4);
        let fold_n = window.residue == 0;
        if (fold_4n && (chunk_4n.len() != chunk_8n.len() || chunk_lookup.len() != chunk_8n.len()))
            || (fold_2n && chunk_2n.len() != chunk_8n.len())
            || (fold_n && chunk_n.len() != chunk_8n.len())
        {
            return Err(Error::InternalInvariant);
        }
        // The fold's dynamic reads come from row-major blocks gathered a
        // few rows at a time (each source column walked sequentially) into
        // buffers this task reuses, instead of ≈ 90 separate column streams
        // per row. Rows of a block: group offset `g` reads its own row at
        // `g + 1`, the `−8` rotation at `g` and the `+8` rotation at `g + 2`.
        let group_rows = FRAME_GROUP_ROWS + 2;
        let mut blocks: Vec<_> = (0..action_count)
            .map(|_| FoldTile {
                columns: execution.buffer(group_rows * GATHER_WIDTH, false),
                carried: [Fp::ZERO; 2],
                frames: execution.buffer(FRAME_GROUP_ROWS * GATE_QUERY_COUNT, false),
                curve_relations: [Fp::ZERO; FRAME_GROUP_ROWS],
                cubics: core::array::from_fn(|_| SinsemillaCubics {
                    current: [Fp::ZERO; 2],
                    next: [Fp::ZERO; 2],
                }),
                sums: core::array::from_fn(|_| generated_expressions::RowSum::new()),
            })
            .collect();
        let mut sigma_block = execution.buffer(FRAME_GROUP_ROWS * SIGMA_GATHER_WIDTH, false);
        let mut fixed_block = execution.buffer(FRAME_GROUP_ROWS * fixed_cosets.len(), false);
        let mut affine_rows = affine::AffineRows::new();
        let mut affine_values = [Fp::ZERO; FRAME_GROUP_ROWS];
        let mut affine_4n: [generated_expressions::RowSum; FRAME_GROUP_ROWS] =
            core::array::from_fn(|_| generated_expressions::RowSum::new());
        let mut selector_scratch =
            [[Fp::ZERO; generated_expressions::PREPARED_GATE_SELECTOR_ROW]; FRAME_GROUP_ROWS];
        let mut tile_coefficients: [Option<generated_expressions::GateRowCoefficients<'_>>;
            FRAME_GROUP_ROWS] = core::array::from_fn(|_| None);
        let rows = chunk_8n.len();
        {
            // Consecutive rows of a residue are `Ω^8 = ω` apart.
            let row_step = extended_omega.pow_u64(EXTENDED_ROTATION_STRIDE as u64);
            let mut coset_point =
                coset_generator.mul(&extended_omega.pow_u64(window.row(0) as u64));
            for (offset, slot_8n) in chunk_8n.iter_mut().enumerate() {
                let row = window.row(offset);
                let next_row = rotated_extended_row(row, 1);
                let group_offset = offset % FRAME_GROUP_ROWS;
                if group_offset == 0 {
                    // Refill the blocks for this group of rows.
                    let group_len = (rows - offset).min(FRAME_GROUP_ROWS);
                    let mut extended_rows = [0usize; FRAME_GROUP_ROWS + 2];
                    extended_rows[0] = rotated_extended_row(row, -1);
                    for (o, extended_row) in
                        extended_rows.iter_mut().enumerate().skip(1).take(group_len)
                    {
                        *extended_row = window.row(offset + o - 1);
                    }
                    extended_rows[group_len + 1] =
                        rotated_extended_row(window.row(offset + group_len - 1), 1);
                    let filled = group_len + 2;
                    for (action, FoldTile { columns: block, .. }) in
                        actions.iter().zip(blocks.iter_mut())
                    {
                        for (slot, column) in action
                            .advice_columns
                            .iter()
                            .chain(core::iter::once(&action.instance_column))
                            .enumerate()
                        {
                            for (o, &extended_row) in extended_rows[..filled].iter().enumerate() {
                                block[o * GATHER_WIDTH + slot] = column[extended_row];
                            }
                        }
                        for (kept_index, set) in action.kept_sets.iter().enumerate() {
                            let slot = GATHER_KEPT_PRODUCT_BASE + kept_index;
                            for (o, &extended_row) in extended_rows[..filled].iter().enumerate() {
                                block[o * GATHER_WIDTH + slot] = set.product[extended_row];
                            }
                        }
                        for (lookup_index, (product, cosets)) in action
                            .lookup_products
                            .iter()
                            .zip(&action.lookup_cosets)
                            .enumerate()
                        {
                            let base = GATHER_LOOKUP_BASE + 3 * lookup_index;
                            for (o, &extended_row) in extended_rows[..filled].iter().enumerate() {
                                let row_base = o * GATHER_WIDTH;
                                if fold_4n {
                                    block[row_base + base] = cosets.permuted_input[extended_row];
                                    block[row_base + base + 1] =
                                        cosets.permuted_table[extended_row];
                                }
                                block[row_base + base + 2] = cosets.compressed_table[extended_row];
                                block[row_base + GATHER_LOOKUP_PRODUCT_BASE + lookup_index] =
                                    product[extended_row];
                            }
                        }
                    }
                    for (column, values) in fixed_cosets.iter().enumerate() {
                        for (o, &extended_row) in extended_rows[1..=group_len].iter().enumerate() {
                            fixed_block[o * fixed_cosets.len() + column] = values[extended_row];
                        }
                    }
                    let mut sigma_column = 0;
                    for set in fixed_sets {
                        for sigma in set.sigma_columns.iter() {
                            for (o, &extended_row) in
                                extended_rows[1..=group_len].iter().enumerate()
                            {
                                sigma_block[o * SIGMA_GATHER_WIDTH + sigma_column] =
                                    sigma[extended_row];
                            }
                            sigma_column += 1;
                        }
                    }
                    if let Some((set_2_sigma, _)) = set_2 {
                        for (o, &extended_row) in extended_rows[1..=group_len].iter().enumerate() {
                            sigma_block[o * SIGMA_GATHER_WIDTH + FIXED_FACTOR_COLUMNS] =
                                set_2_sigma[extended_row];
                        }
                    }
                    for r in 0..group_len {
                        let row = window.row(offset + r);
                        let fixed_query = |slot: usize| {
                            let (kind, query) = GATE_QUERY_DESCRIPTORS[slot];
                            debug_assert_eq!(kind, QueryKind::Fixed);
                            fixed_block[r * fixed_cosets.len()
                                + sensei_shared::queries::FIXED_QUERIES[query].column]
                        };
                        let selectors = if let Some(prepared) = gate_selectors {
                            &prepared[row]
                        } else {
                            let queries =
                                core::array::from_fn(|slot| match GATE_QUERY_DESCRIPTORS[slot].0 {
                                    QueryKind::Fixed => fixed_query(slot),
                                    _ => Fp::ZERO,
                                });
                            selector_scratch[r] =
                                generated_expressions::prepare_gate_selectors(&queries);
                            &selector_scratch[r]
                        };
                        tile_coefficients[r] =
                            Some(generated_expressions::GateRowCoefficients::for_row(
                                selectors,
                                generated_expressions::ROW_COEFFICIENT_QUERY_SLOTS.map(fixed_query),
                                slot_powers,
                                y_powers,
                                &constants.gate_challenge_coefficients,
                                shared_affine,
                            ));
                    }
                    for FoldTile {
                        columns: block,
                        carried,
                        frames,
                        cubics,
                        curve_relations,
                        sums,
                    } in &mut blocks
                    {
                        for r in 0..group_len {
                            let frame: &mut [Fp; GATE_QUERY_COUNT] = (&mut frames
                                [r * GATE_QUERY_COUNT..(r + 1) * GATE_QUERY_COUNT])
                                .try_into()
                                .unwrap();
                            frame_gather::fill_frame(
                                frame,
                                block,
                                &fixed_block,
                                fixed_cosets.len(),
                                r,
                            );
                            curve_relations[r] =
                                generated_expressions::first_curve_relation(&|slot| frame[slot]);
                            cubics[r] = SinsemillaCubics {
                                current: if offset + r == 0 {
                                    SinsemillaCubics::at_row(frame)
                                } else {
                                    *carried
                                },
                                next: SinsemillaCubics::at_next_row(frame),
                            };
                            *carried = cubics[r].next;
                            sums[r] = generated_expressions::RowSum::new();
                        }
                    }
                    // Keep each smaller instruction working set hot across the tile.
                    // Row accumulators retain their unreduced limbs between families.
                    macro_rules! family {
                        ($family:literal) => {
                            for FoldTile { frames, cubics, curve_relations, sums, .. } in &mut blocks {
                                for r in 0..group_len {
                                    let frame = frames[r * GATE_QUERY_COUNT..].first_chunk::<GATE_QUERY_COUNT>().unwrap();
                                    let selectors = gate_selectors.map_or(&selector_scratch[r], |prepared| &prepared[window.row(offset + r)]);
                                    let coefficients = tile_coefficients[r].as_ref().unwrap();
                                    if shared_affine {
                                        generated_expressions::evaluate_gate_family::<true, $family>(frame, &cubics[r], &curve_relations[r], selectors, coefficients, slot_powers, &mut sums[r]);
                                    } else {
                                        generated_expressions::evaluate_gate_family::<false, $family>(frame, &cubics[r], &curve_relations[r], selectors, coefficients, slot_powers, &mut sums[r]);
                                    }
                                }
                            }
                        };
                    }
                    family!(0);
                    family!(1);
                    family!(2);
                    family!(3);
                    family!(4);
                    family!(5);
                    if shared_affine {
                        // Keep the shared affine instruction working set hot
                        // across the tile, retaining only its finished values.
                        for r in 0..group_len {
                            affine_rows.advance(
                                offset + r == 0,
                                &constants.action_weights,
                                |action, neighbour, column| {
                                    blocks[action].columns[(r + neighbour) * GATHER_WIDTH + column]
                                },
                            );
                            let selectors = gate_selectors
                                .map_or(&selector_scratch[r], |prepared| {
                                    &prepared[window.row(offset + r)]
                                });
                            let affine_frame = affine_rows.frame();
                            affine_values[r] = generated_expressions::evaluate_affine_gates::<true>(
                                &affine_frame,
                                &constants.weight_sum,
                                selectors,
                                tile_coefficients[r]
                                    .as_ref()
                                    .ok_or(Error::InternalInvariant)?,
                                slot_powers,
                            );
                            if fold_4n {
                                let frame = blocks[0].frames[r * GATE_QUERY_COUNT..]
                                    .first_chunk::<GATE_QUERY_COUNT>()
                                    .unwrap();
                                generated_expressions::evaluate_affine_gates_4n::<true>(
                                    &|slot| match actions.first().unwrap().query_sources[slot] {
                                        FoldColumnSource::Fixed(_) => {
                                            frame[slot].mul(&constants.weight_sum)
                                        }
                                        _ => affine_frame[slot],
                                    },
                                    &constants.weight_sum,
                                    selectors,
                                    &constants.gate_coefficients_4n,
                                    &mut affine_4n[r],
                                );
                            }
                        }
                    }
                }
                // This row's gathered rows: `here` is the row, `before` and
                // `after` its rotation neighbours.
                let before = group_offset * GATHER_WIDTH;
                let here = before + GATHER_WIDTH;
                let after = here + GATHER_WIDTH;
                let sigma_row = group_offset * SIGMA_GATHER_WIDTH;
                let mut acc_8n = <Fp>::ZERO;
                let mut gates_4n = if shared_affine && fold_4n {
                    core::mem::replace(
                        &mut affine_4n[group_offset],
                        generated_expressions::RowSum::new(),
                    )
                } else {
                    generated_expressions::RowSum::new()
                };
                let mut acc_lookup = <Fp>::ZERO;
                let mut acc_2n = <Fp>::ZERO;
                // Boundary selectors are shared by every Action. Accumulate
                // their weighted bodies before applying l_0, l_last, or
                // active_rows once, with one reduction per body sum.
                let mut boundary_n = generated_expressions::RowSum::new();
                let mut boundary_2n = generated_expressions::RowSum::new();
                let mut rules_2n = generated_expressions::RowSum::new();
                let gate_selector_row = gate_selectors
                    .map_or(&selector_scratch[group_offset], |prepared| &prepared[row]);
                // Fixed columns contribute complete factors, including β/γ.
                // Sharing their products uses no inverses and preserves zeros.
                let mut fixed_products: [Option<(Fp, Fp)>; KEPT_PERMUTATION_SETS] =
                    [None; KEPT_PERMUTATION_SETS];
                {
                    let mut column = 0;
                    for (set_index, set) in fixed_sets.iter().enumerate() {
                        for (source, beta_delta) in set.column_sources.iter().zip(set.beta_deltas) {
                            left_offsets[column] =
                                beta.mul(&sigma_block[sigma_row + column]).add(gamma);
                            right_offsets[column] = beta_delta.mul(&coset_point).add(gamma);
                            if let FoldColumnSource::Fixed(c) = *source {
                                let value = fixed_block[group_offset * fixed_cosets.len() + c];
                                let left = value.add(&left_offsets[column]);
                                let right = value.add(&right_offsets[column]);
                                fixed_products[set_index] = Some(match fixed_products[set_index] {
                                    Some((l, r)) => (l.mul(&left), r.mul(&right)),
                                    None => (left, right),
                                });
                            }
                            column += 1;
                        }
                    }
                }
                // The lookup inputs' row coefficients (fixed columns × θ)
                // are formed once per row and shared by every Action, whose
                // compressed inputs are evaluated here rather than read from
                // retained cosets.
                let fixed_columns: [_; sensei_shared::dimensions::FIXED_COLUMNS] =
                    core::array::from_fn(|column| GatheredColumn::<
                        { sensei_shared::dimensions::FIXED_COLUMNS },
                    > {
                        block: &fixed_block,
                        column,
                    });
                let lookup_row_coefficients = constants.lookup_input_kernels.map(|kernel| {
                    LookupInputRowCoefficients::at_row(
                        kernel,
                        &constants.lookup_constants,
                        &constants.theta,
                        &fixed_columns,
                        group_offset,
                    )
                });
                let lookup_right_weights: [_; fold_order::LOOKUP_COUNT] =
                    core::array::from_fn(|lookup| {
                        lookup_rule_powers[lookup].neg().mul(
                            &blocks[0].columns[here + GATHER_LOOKUP_BASE + 3 * lookup + 2]
                                .add(gamma),
                        )
                    });
                let (set_2_left_offset, set_2_right_offset) = match set_2 {
                    Some((_, set_2_beta_delta)) if fold_2n => (
                        beta.mul(&sigma_block[sigma_row + FIXED_FACTOR_COLUMNS])
                            .add(gamma),
                        set_2_beta_delta.mul(&coset_point).add(gamma),
                    ),
                    _ => (<Fp>::ZERO, <Fp>::ZERO),
                };
                for (action_index, action) in actions.iter().enumerate() {
                    let FoldTile {
                        columns: block,
                        frames,
                        cubics,
                        curve_relations,
                        sums,
                        ..
                    } = &mut blocks[action_index];
                    let frame = frames[group_offset * GATE_QUERY_COUNT..]
                        .first_chunk::<GATE_QUERY_COUNT>()
                        .unwrap();
                    let cubics = &cubics[group_offset];
                    let mut row_sum = core::mem::replace(
                        &mut sums[group_offset],
                        generated_expressions::RowSum::new(),
                    );
                    // The permutation rules and lookup right branches share
                    // one reduction and one active-row factor on 8N.
                    let mut rules = generated_expressions::RowSum::new();
                    let mut lookup_left = generated_expressions::RowSum::new();
                    for (kept_index, set) in action.kept_sets.iter().enumerate() {
                        let mut left = block[after + GATHER_KEPT_PRODUCT_BASE + kept_index];
                        let mut right = block[here + GATHER_KEPT_PRODUCT_BASE + kept_index];
                        if let Some((fixed_left, fixed_right)) = fixed_products[kept_index] {
                            left = left.mul(&fixed_left);
                            right = right.mul(&fixed_right);
                        }
                        for (slot, source) in set.column_sources.iter().enumerate() {
                            let column = kept_index * PERMUTATION_CHUNK_LEN + slot;
                            let value = match *source {
                                FoldColumnSource::Advice(c) => block[here + c],
                                FoldColumnSource::Fixed(_) => continue,
                                FoldColumnSource::Instance => block[here + ADVICE_COLUMNS],
                            };
                            left = left.mul(&value.add(&left_offsets[column]));
                            right = right.mul(&value.add(&right_offsets[column]));
                        }
                        rules.add_product(&left.sub(&right), &rule_powers[kept_index]);
                    }
                    for (lookup_index, lookup_rule_power) in lookup_rule_powers.iter().enumerate() {
                        let compressed_input = lookup_row_coefficients
                            .get(lookup_index)
                            .ok_or(Error::InternalInvariant)?
                            .evaluate(
                                &constants.lookup_constants,
                                &core::array::from_fn::<_, ADVICE_COLUMNS, _>(|column| {
                                    GatheredColumn::<GATHER_WIDTH> { block, column }
                                }),
                                group_offset + 1,
                                group_offset + 2,
                                &cubics.current,
                            );
                        let lookup_base = GATHER_LOOKUP_BASE + 3 * lookup_index;
                        let product_slot = GATHER_LOOKUP_PRODUCT_BASE + lookup_index;
                        if fold_4n {
                            let left = block[after + product_slot]
                                .mul(&block[here + lookup_base].add(beta))
                                .mul(&block[here + lookup_base + 1].add(gamma));
                            lookup_left.add_product(&left, lookup_rule_power);
                        }
                        let right = block[here + product_slot].mul(&compressed_input.add(beta));
                        rules.add_product(&right, &lookup_right_weights[lookup_index]);
                    }
                    row_sum.add_product(&rules.finish(), &active_rows[row]);
                    if shared_affine && action_index + 1 == action_count {
                        // The shared affine value's powers already carry the
                        // rule-block offset; it joins the last Action's row.
                        row_sum.add_term(&affine_values[group_offset]);
                    }
                    // The Action blocks combine by one `y^215` step on the
                    // finished row values.
                    let row_value = row_sum.finish();
                    acc_8n = if action_index == 0 {
                        row_value
                    } else {
                        acc_8n.mul_add(y_action_step, &row_value)
                    };
                    if fold_4n {
                        let left = lookup_left.finish();
                        acc_lookup = if action_index == 0 {
                            left
                        } else {
                            acc_lookup.mul_add(y_action_step, &left)
                        };
                        gates_4n.add_product(
                            &curve_relations[group_offset],
                            &Fp::sum_of_products(
                                &[frame[42], frame[43]],
                                action.gate_curve_powers_4n,
                            ),
                        );
                    }
                    if fold_2n {
                        generated_expressions::evaluate_gates_2n(
                            &|slot| frame[slot],
                            action.gate_powers_2n,
                            &mut acc_2n,
                        );
                        // The singleton set's product lives on the 2N class
                        // coset; this row and its `+8` rotation lie on it.
                        let z = action.singleton_product.at_extended_row(row);
                        // Permutation boundary: (z_last² − z_last)·l_last.
                        boundary_2n.add_product(&action.perm_l_last_power, &z.square().sub(&z));
                        // The singleton chunk's degree-3 product rule.
                        let rule = action
                            .singleton_product
                            .at_extended_row(next_row)
                            .mul_sub_product(
                                &action.set_2_values[row].add(&set_2_left_offset),
                                &z,
                                &action.set_2_values[row].add(&set_2_right_offset),
                            );
                        rules_2n.add_product(&action.set_2_rule_power, &rule);
                        for (lookup_index, l_last_power) in
                            action.lookup_l_last_powers.iter().enumerate()
                        {
                            let lookup_base = GATHER_LOOKUP_BASE + 3 * lookup_index;
                            // Lookup boundary: (p² − p)·l_last.
                            let p = block[here + GATHER_LOOKUP_PRODUCT_BASE + lookup_index];
                            boundary_2n.add_product(l_last_power, &p.square().sub(&p));
                            // Permuted continuity: (a′ − s′)·(a′ − a′₋₁)·active,
                            // the previous row being the gathered `−8` neighbour.
                            let permuted_input = block[here + lookup_base];
                            let difference = permuted_input.sub(&block[here + lookup_base + 1]);
                            let step = permuted_input.sub(&block[before + lookup_base]);
                            rules_2n.add_product(
                                &action.lookup_continuity_powers[lookup_index],
                                &difference.mul(&step),
                            );
                        }
                    }
                    if fold_n {
                        // Permutation boundary: (1 − z_0)·l_0.
                        boundary_n.add_product(
                            &action.perm_l_0_power,
                            &<Fp>::ONE.sub(&action.kept_products[0][row]),
                        );
                        // Continuity: (z_set − z_{set−1}(ω^{−(b+1)}X))·l_0.
                        let last_row = rotated_extended_row(row, -((BLINDING_FACTORS + 1) as i32));
                        for (continuity_index, continuity_power) in
                            action.continuity_powers.iter().enumerate()
                        {
                            let set_index = continuity_index + 1;
                            // Every set but the last is kept; the singleton's
                            // continuity reads it on the 2N coset (this row is
                            // a multiple of 8) against the kept set before it.
                            let current = if set_index < KEPT_PERMUTATION_SETS {
                                action.kept_products[set_index][row]
                            } else {
                                action.singleton_product.at_extended_row(row)
                            };
                            boundary_n.add_product(
                                continuity_power,
                                &current.sub(&action.kept_products[set_index - 1][last_row]),
                            );
                        }
                        for (lookup_index, (product, cosets)) in action
                            .lookup_products
                            .iter()
                            .zip(&action.lookup_cosets)
                            .enumerate()
                        {
                            // Lookup boundary: (1 − p)·l_0.
                            boundary_n.add_product(
                                &action.lookup_l_0_powers[lookup_index],
                                &<Fp>::ONE.sub(&product[row]),
                            );
                            // Permuted boundary: (a′ − s′)·l_0.
                            boundary_n.add_product(
                                &action.lookup_permuted_l_0_powers[lookup_index],
                                &cosets.permuted_input[row].sub(&cosets.permuted_table[row]),
                            );
                        }
                    }
                }
                *slot_8n = acc_8n.mul(&scale_8n[row % 8]);
                if fold_4n {
                    let frame = blocks[0].frames[group_offset * GATE_QUERY_COUNT..]
                        .first_chunk::<GATE_QUERY_COUNT>()
                        .unwrap();
                    if !shared_affine {
                        generated_expressions::evaluate_affine_gates_4n::<false>(
                            &|slot| frame[slot],
                            &Fp::ONE,
                            gate_selector_row,
                            &constants.gate_coefficients_4n,
                            &mut gates_4n,
                        );
                    }
                    chunk_4n[offset] = gates_4n.finish().mul(&scale_4n[(row % 8) / 2]);
                    chunk_lookup[offset] = acc_lookup
                        .mul(&active_rows[row])
                        .mul(&scale_4n[(row % 8) / 2]);
                }
                if fold_2n {
                    acc_2n = acc_2n.add(&<Fp>::sum_of_products(
                        &[boundary_2n.finish(), rules_2n.finish()],
                        &[l_last[row], active_rows[row]],
                    ));
                    chunk_2n[offset] = acc_2n.mul(&scale_2n[(row % 8) / 4]);
                }
                if fold_n {
                    chunk_n[offset] = boundary_n.finish().mul(&l_0[row]).mul(scale_n);
                }
                coset_point = coset_point.mul(&row_step);
            }
        }
        Ok(())
    }
}
