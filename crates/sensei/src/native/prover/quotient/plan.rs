//! Validate fold inputs and prepare the shared challenge powers and Action plans.

use super::*;

/// Per-action slot positions (in the frozen fold order) of the non-gate
/// terms the class split carves out of the 8N accumulator: fixed-shape
/// arrays derived from the [`fold_order`] family metadata, so the slots are a
/// compile-time constant rather than per-proof vectors.
#[derive(Clone, Copy)]
pub(super) struct SmallClassSlots {
    perm_l_0: usize,
    perm_l_last: usize,
    continuity: [usize; fold_order::PERMUTATION_SET_COUNT - 1],
    set_2_rule: usize,
    lookup_l_0: [usize; fold_order::LOOKUP_COUNT],
    lookup_l_last: [usize; fold_order::LOOKUP_COUNT],
    lookup_permuted_l_0: [usize; fold_order::LOOKUP_COUNT],
    lookup_continuity: [usize; fold_order::LOOKUP_COUNT],
}

impl SmallClassSlots {
    /// The frozen fold order's carved slots.
    pub(super) const FROZEN: Self = Self {
        perm_l_0: fold_order::permutation_l_0(),
        perm_l_last: fold_order::permutation_l_last(),
        continuity: fold_order::continuity_slots(),
        set_2_rule: fold_order::rule(fold_order::PERMUTATION_SET_COUNT - 1),
        lookup_l_0: fold_order::lookup_slots(fold_order::LOOKUP_L_0),
        lookup_l_last: fold_order::lookup_slots(fold_order::LOOKUP_L_LAST),
        lookup_permuted_l_0: fold_order::lookup_slots(fold_order::LOOKUP_PERMUTED_L_0),
        lookup_continuity: fold_order::lookup_slots(fold_order::LOOKUP_PERMUTED_CONTINUITY),
    };
}

pub(super) fn build_fold_plan<'a>(
    target: &'a FixedTarget,
    inputs: FoldInputs<'a>,
    slots: SmallClassSlots,
    execution: Execution<'_>,
) -> Result<FoldPlan<'a>, Error> {
    let advice_cosets = &inputs.advice_cosets;
    let fixed_cosets = &inputs.fixed_cosets;
    let sigma_cosets = &inputs.sigma_cosets;
    let beta_deltas = &inputs.beta_deltas;
    let y = inputs.y;
    let total_terms = inputs.total_terms;
    let action_count = total_terms / fold_order::TERMS_PER_ACTION;
    if action_count * fold_order::TERMS_PER_ACTION != total_terms || action_count == 0 {
        return Err(Error::InternalInvariant);
    }
    let queries = target.queries();
    if target
        .gate_selectors()
        .is_some_and(|rows| rows.len() != EXTENDED_N)
        || !coset_query_columns_exist(queries.fixed(), fixed_cosets.len())
        || advice_cosets
            .iter()
            .any(|advice| !coset_query_columns_exist(queries.advice(), advice.len()))
        || !coset_query_columns_exist(queries.instance(), 1)
    {
        return Err(Error::InternalInvariant);
    }

    let set_2_start =
        (target.permutation_columns().len() / PERMUTATION_CHUNK_LEN) * PERMUTATION_CHUNK_LEN;
    let set_2_column = target
        .permutation_columns()
        .get(set_2_start)
        .ok_or(Error::InternalInvariant)?;
    let set_2_sigma = sigma_cosets
        .get(set_2_start)
        .copied()
        .ok_or(Error::InternalInvariant)?;
    let set_2_beta_delta = *beta_deltas
        .get(set_2_start)
        .ok_or(Error::InternalInvariant)?;

    // Udon prepares independent power lanes; gate-local powers reuse the prefix.
    let mut y_ladder = execution.buffer(total_terms, false);
    y_ladder[0] = <Fp>::ONE;
    EvaluationPlan::prepare(&y, &mut y_ladder[1..]);
    let mut y_powers = [<Fp>::ONE; generated_expressions::MAX_GATE_CONSTRAINTS + 1];
    y_powers.copy_from_slice(&y_ladder[..=generated_expressions::MAX_GATE_CONSTRAINTS]);

    // The frozen argument shape: two full permutation chunks plus the
    // singleton fixed-column chunk (whose degree-3 rule folds at 2N), and
    // three lookups.
    let permutation_set_count = target
        .permutation_columns()
        .len()
        .div_ceil(PERMUTATION_CHUNK_LEN);
    let lookup_count = target.lookups().len();
    debug_assert_eq!(permutation_set_count, 3);
    debug_assert_eq!(
        target.permutation_columns().len() % PERMUTATION_CHUNK_LEN,
        1
    );
    debug_assert_eq!(lookup_count, 3);
    let y_37 = y_powers[14].square().mul(&y_powers[9]);
    let mut action_weights = execution.buffer(action_count, false);
    for (action, weight) in action_weights.iter_mut().enumerate() {
        *weight = y_ladder[fold_order::TERMS_PER_ACTION * (action_count - 1 - action)];
    }
    let weight_sum = action_weights
        .iter()
        .fold(<Fp>::ZERO, |sum, weight| sum.add(weight));
    // Absolute in-Action slot powers: a term at slot `i` of an Action's
    // block weighs `y^(TERMS_PER_ACTION − 1 − i)`, and the Action blocks
    // combine by `y^TERMS_PER_ACTION` steps. Field arithmetic is exact, so
    // the row value is the sequential Horner fold's; the carved slots (the
    // small-class terms) simply contribute nothing on the 8N pass.
    let in_action_power = |slot: usize| y_ladder[fold_order::TERMS_PER_ACTION - 1 - slot];
    let slot_powers = core::array::from_fn(in_action_power);
    let rule_powers = core::array::from_fn(|set| in_action_power(fold_order::rule(set)));
    let lookup_rule_powers = core::array::from_fn(|lookup| {
        in_action_power(fold_order::lookup(lookup, fold_order::LOOKUP_RULE))
    });
    let y_action_step = y_ladder[fold_order::TERMS_PER_ACTION - 1].mul(&y);

    // Constant vanishing divisor per stride-8 sub-coset:
    // `Z_H(ζ·g^r·ω^k) = ζ^N·μ^r − 1` with `μ = g^N` (pinned against the
    // telescope by `per_subcoset_vanishing_constants_match_the_telescope`);
    // each class's stride keeps every other residue of the next class up.
    let scale_8n = *target.domain().vanishing_inverses();
    let scale_4n = [scale_8n[0], scale_8n[2], scale_8n[4], scale_8n[6]];
    let scale_2n = [scale_8n[0], scale_8n[4]];
    let scale_n = scale_8n[0];

    let lookup_constants = LookupKernelConstants::load();
    let theta_constants = ThetaConstants::new(inputs.theta, &lookup_constants);
    let lookup_input_kernels: [LookupInputRowKernel; fold_order::LOOKUP_COUNT] = (0
        ..fold_order::LOOKUP_COUNT)
        .map(|lookup_index| lookup_input_row_kernel(target, lookup_index))
        .collect::<Result<Vec<_>, Error>>()?
        .try_into()
        .map_err(|_| Error::InternalInvariant)?;

    let constants = FoldConstants {
        set_2_column,
        set_2_sigma,
        set_2_beta_delta,
        y_ladder,
        y_powers,
        gate_challenge_coefficients: generated_expressions::GateChallengeCoefficients::new(
            &slot_powers,
            y_37,
            y,
        ),
        gate_coefficients_4n: generated_expressions::Gate4NCoefficients::new(
            generated_expressions::GATE_PROGRAMS_4N.map(|slot| slot_powers[slot]),
        ),
        action_weights,
        weight_sum,
        slot_powers,
        rule_powers,
        lookup_rule_powers,
        y_action_step,
        scale_8n,
        scale_4n,
        scale_2n,
        scale_n,
        lookup_input_kernels,
        theta: theta_constants,
        lookup_constants,
    };
    // Validate every Action's views once and keep the descriptors; the row
    // tasks resolve from them without rebuilding.
    let action_plans = build_action_plans(target, &inputs, &constants, &slots)?;
    Ok(FoldPlan {
        target,
        inputs,
        constants: Arc::new(constants),
        action_plans: Arc::new(action_plans),
    })
}

/// Resolves one fold column to its source among the shared inputs,
/// validating that it exists with the extended-coset length (the tiled
/// records carry that length by construction).
fn fold_column_source<'a>(
    column: &PermutationColumn,
    advice: &[ExtendedCoset],
    fixed: &[FpCosetView<'a>],
) -> Result<FoldColumnSource, Error> {
    use crate::native::target::ColumnKind;
    let exists = match column.kind {
        ColumnKind::Advice => advice.get(column.index).is_some(),
        ColumnKind::Fixed => fixed.get(column.index).is_some(),
        ColumnKind::Instance => column.index == 0,
    };
    if !exists {
        return Err(Error::InternalInvariant);
    }
    Ok(match column.kind {
        ColumnKind::Advice => FoldColumnSource::Advice(column.index),
        ColumnKind::Fixed => FoldColumnSource::Fixed(column.index),
        ColumnKind::Instance => FoldColumnSource::Instance,
    })
}

/// Validates every Action's fold inputs once and records where each view
/// comes from together with its challenge weights, so [`rows`] resolves its
/// borrowed Action views without repeating this work.
fn build_action_plans(
    target: &FixedTarget,
    inputs: &FoldInputs,
    constants: &FoldConstants,
    slots: &SmallClassSlots,
) -> Result<Vec<ActionPlan>, Error> {
    let fixed_cosets = inputs.fixed_cosets.as_slice();
    let sigma_cosets = inputs.sigma_cosets.as_slice();
    let beta_deltas = inputs.beta_deltas.as_slice();
    let (total_terms, terms_per_action) = (inputs.total_terms, inputs.terms_per_action);
    let y_ladder = constants.y_ladder.as_slice();
    let queries = target.queries();
    let action_count = inputs.advice_cosets.len();
    if inputs.instance_cosets.len() != action_count
        || inputs.permutation_cosets.len() != action_count
        || inputs.lookup_product_cosets.len() != action_count
        || inputs.lookup_cosets.len() != action_count
        || sigma_cosets.len() != target.permutation_columns().len()
        || beta_deltas.len() != target.permutation_columns().len()
    {
        return Err(Error::InternalInvariant);
    }

    let mut plans = Vec::with_capacity(action_count);
    for action_index in 0..action_count {
        let advice = inputs.advice_cosets[action_index].as_slice();
        // The row tasks resolve fixed-shape view arrays from these records.
        if advice.len() != ADVICE_COLUMNS
            || inputs.lookup_cosets[action_index].len() != fold_order::LOOKUP_COUNT
        {
            return Err(Error::InternalInvariant);
        }
        // The gate query frame: the same resolution and validation the row
        // tasks used to repeat, kept as sources.
        let mut query_sources = [FoldColumnSource::Instance; GATE_QUERY_COUNT];
        let mut query_rotations = [0; GATE_QUERY_COUNT];
        for (frame_index, &(kind, query_index)) in GATE_QUERY_DESCRIPTORS.iter().enumerate() {
            let query_set = match kind {
                QueryKind::Fixed => queries.fixed(),
                QueryKind::Advice => queries.advice(),
                QueryKind::Instance => queries.instance(),
            };
            let query = query_set.get(query_index).ok_or(Error::InternalInvariant)?;
            let (source, exists) = match kind {
                QueryKind::Fixed => (
                    FoldColumnSource::Fixed(query.column),
                    fixed_cosets.get(query.column).is_some(),
                ),
                QueryKind::Advice => (
                    FoldColumnSource::Advice(query.column),
                    advice.get(query.column).is_some(),
                ),
                QueryKind::Instance => (FoldColumnSource::Instance, query.column == 0),
            };
            if !exists {
                return Err(Error::InternalInvariant);
            }
            query_sources[frame_index] = source;
            query_rotations[frame_index] = match query.rotation {
                -1 => 0,
                0 => 1,
                1 => 2,
                _ => return Err(Error::InternalInvariant),
            };
        }

        // Only the full permutation chunks fold at 8N; the singleton chunk's
        // degree-3 rule folds on the 2N class.
        let mut kept_sets = [KeptSetPlan {
            set_index: 0,
            columns: [FoldColumnSource::Instance; PERMUTATION_CHUNK_LEN],
            first_column: 0,
        }; KEPT_PERMUTATION_SETS];
        let mut kept_count = 0;
        for (set_index, columns) in target
            .permutation_columns()
            .chunks(PERMUTATION_CHUNK_LEN)
            .enumerate()
        {
            if columns.len() == 1 {
                continue;
            }
            if columns.len() != PERMUTATION_CHUNK_LEN || set_index >= KEPT_PERMUTATION_SETS {
                return Err(Error::InternalInvariant);
            }
            let first_column = set_index * PERMUTATION_CHUNK_LEN;
            let mut sources = [FoldColumnSource::Instance; PERMUTATION_CHUNK_LEN];
            for (slot, column) in columns.iter().enumerate() {
                sources[slot] = fold_column_source(column, advice, fixed_cosets)?;
            }
            *kept_sets
                .get_mut(kept_count)
                .ok_or(Error::InternalInvariant)? = KeptSetPlan {
                set_index,
                columns: sources,
                first_column,
            };
            kept_count += 1;
        }
        if kept_count != KEPT_PERMUTATION_SETS {
            return Err(Error::InternalInvariant);
        }
        let set_2_source = fold_column_source(constants.set_2_column, advice, fixed_cosets)?;

        let power =
            |slot: usize| y_ladder[total_terms - 1 - (action_index * terms_per_action + slot)];
        plans.push(ActionPlan {
            query_sources,
            query_rotations,
            kept_sets,
            set_2_source,
            gate_powers_2n: generated_expressions::GATE_PROGRAMS_2N.map(&power),
            gate_curve_powers_4n: core::array::from_fn(|i| {
                power(generated_expressions::GATE_PROGRAMS_4N[i])
            }),
            perm_l_0_power: power(slots.perm_l_0),
            perm_l_last_power: power(slots.perm_l_last),
            set_2_rule_power: power(slots.set_2_rule),
            continuity_powers: slots.continuity.map(&power),
            lookup_l_0_powers: slots.lookup_l_0.map(&power),
            lookup_l_last_powers: slots.lookup_l_last.map(&power),
            lookup_permuted_l_0_powers: slots.lookup_permuted_l_0.map(&power),
            lookup_continuity_powers: slots.lookup_continuity.map(&power),
        });
    }
    Ok(plans)
}
