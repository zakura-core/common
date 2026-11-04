//! Quotient construction over the extended domain.
//!
//! Column expansions publish residues to a degree-classed constraint fold.
//! Completed classes enter interpolation on the same task queue. A request
//! that fits one window can overlap piece commitments with interpolation;
//! larger requests combine window coefficients before committing. Opening
//! coefficients and blinds survive the transcript-ordered commitment writes.
//!
//! [`plan`] validates inputs and prepares challenge powers; [`rows`] resolves
//! the row views and folds each window. [`run`] schedules their producers and
//! consumers, and [`affine`] supplies the shared affine frames.

use crate::native::try_array_from_fn;

use crate::Error;
use crate::native::buffer::Buffer;
use crate::native::commitment::normalized;
use crate::native::curve::VestaPoint;
use crate::native::evaluation::{
    EXTENDED_ROTATION_STRIDE, coset_query_columns_exist, rotated_extended_row,
};
use crate::native::field::Fp;
use crate::native::generated_expressions;
use crate::native::generated_expressions::{
    GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, QueryKind, SinsemillaCubics,
};
use crate::native::polynomial::{FpClass2NView, FpCosetView, SharedPoly};
use crate::native::randomness::IpaMaskRandomness;
use crate::native::target::{
    ADVICE_COLUMNS, BLINDING_FACTORS, EXTENDED_N, FixedTarget, K, N, PERMUTATION_CHUNK_LEN,
    PERMUTATION_COLUMN_COUNT, PermutationColumn, QUOTIENT_PIECES,
};
use crate::native::worker::Execution;
use alloc::{sync::Arc, vec::Vec};
use sensei_shared::FIXED_COLUMNS;
use udon::polynomial::EvaluationPlan;

mod affine;
mod plan;
mod rows;
mod run;

use plan::{SmallClassSlots, build_fold_plan};

/// The coefficient generators the sparse IPA mask's `α_i` multiply:
/// `G_{2^i}` for each doubling exponent, in ascending order.
/// See [`IpaMaskEarly`] for the split commitment and its late constant term.
const IPA_MASK_GENERATOR_INDICES: [u32; K as usize] = {
    let mut indices = [0u32; K as usize];
    let mut exponent = 0;
    while exponent < K as usize {
        indices[exponent] = 1u32 << exponent;
        exponent += 1;
    }
    indices
};

use super::inventory::quotient_stage;
use super::lookup::{
    LookupInputRowCoefficients, LookupInputRowKernel, LookupKernelConstants, ThetaConstants,
    lookup_input_row_kernel, share_compressed_tables,
};
use super::{
    AdvicePrefix, Class2NCoset, ExtendedCoset, FOLD_CHUNK_ROWS, IpaMaskEarly, LagrangeFormInput,
    LookupCosets, LookupPrefix, LookupProductPrefix, PermutationPrefix, PermutedLookupCoefficients,
    ProductCoset, ProverPrefix, QuotientPiece, QuotientPrefix, VanishingPrefix, fold_order,
    split_product_openings,
};

/// One window's quotient contribution, or the sum of consecutive windows.
///
/// Coefficients are unblinded. `commitments` is empty and `mask` is identity
/// when preparation defers commitments. Opening records stay in Action order.
struct PreparedQuotient {
    pieces: Vec<Buffer<Fp>>,
    commitments: Vec<crate::native::curve::VestaProjective>,
    mask: crate::native::curve::VestaProjective,
    advice_coefficients: Vec<Vec<SharedPoly>>,
    advice_blinds: Vec<[Fp; ADVICE_COLUMNS]>,
    permuted_lookup_coefficients: Vec<[PermutedLookupCoefficients; fold_order::LOOKUP_COUNT]>,
    permutation_openings: super::ProductOpenings<{ fold_order::PERMUTATION_SET_COUNT }>,
    lookup_product_openings: super::ProductOpenings<{ fold_order::LOOKUP_COUNT }>,
}
impl PreparedQuotient {
    fn empty(execution: Execution<'_>) -> Self {
        Self {
            pieces: (0..QUOTIENT_PIECES)
                .map(|_| execution.buffer(N, true))
                .collect(),
            commitments: Vec::new(),
            mask: crate::native::curve::VestaProjective::IDENTITY,
            advice_coefficients: Vec::new(),
            advice_blinds: Vec::new(),
            permuted_lookup_coefficients: Vec::new(),
            permutation_openings: Vec::new(),
            lookup_product_openings: Vec::new(),
        }
    }
    fn add_window(&mut self, window: Self, weight: Fp) {
        assert_eq!(self.pieces.len(), window.pieces.len());
        for (sum, piece) in self.pieces.iter_mut().zip(window.pieces) {
            for (sum, value) in sum.iter_mut().zip(piece.iter()) {
                *sum = sum.add(&value.mul(&weight));
            }
        }
        self.advice_coefficients.extend(window.advice_coefficients);
        self.advice_blinds.extend(window.advice_blinds);
        self.permuted_lookup_coefficients
            .extend(window.permuted_lookup_coefficients);
        self.permutation_openings
            .extend(window.permutation_openings);
        self.lookup_product_openings
            .extend(window.lookup_product_openings);
    }
}

impl ProverPrefix<'_> {
    /// Folds the stage records for one contiguous `action_range`.
    ///
    /// The caller bounds the range by [`crate::sizing::ACTION_WINDOW`]. With
    /// `commit`, overlaps commitments with interpolation; otherwise returns
    /// unblinded coefficients to combine under the global challenge weights.
    /// Does not write to the transcript or draw randomness in either mode.
    #[allow(clippy::too_many_arguments)] // each stage's pre-sampled randomness arrives as its own labeled record
    fn prepare_quotient_window(
        &mut self,
        advice: AdvicePrefix,
        lookup: LookupPrefix,
        permutations: PermutationPrefix,
        lookup_products: LookupProductPrefix,
        vanishing: &VanishingPrefix,
        action_range: core::ops::Range<usize>,
        commit: bool,
        piece_blinds: &[Fp; QUOTIENT_PIECES],
        ipa_mask: &IpaMaskRandomness,
    ) -> Result<PreparedQuotient, Error> {
        #[cfg(test)]
        let mut timing = crate::native::stage_timing::QuotientRecorder::begin();
        let target = self.target;
        let action_count = action_range.len();
        let permutation_set_count = target
            .permutation_columns()
            .len()
            .div_ceil(PERMUTATION_CHUNK_LEN);
        if advice.values.len() != action_count
            || advice.blinds.len() != action_count
            || advice
                .values
                .iter()
                .any(|columns| columns.len() != ADVICE_COLUMNS)
            || lookup.lookups.len() != action_count
            || lookup
                .lookups
                .iter()
                .any(|lookups| lookups.len() != target.lookups().len())
            || permutations.products.len() != action_count
            || lookup_products.products.len() != action_count
            || piece_blinds.len() != QUOTIENT_PIECES
            || target.boundaries().l_0().len() != EXTENDED_N
            || target.boundaries().l_last().len() != EXTENDED_N
            || target.boundaries().active_rows().len() != EXTENDED_N
            || target.permutation_identities().deltas().len() != target.permutation_columns().len()
        {
            return Err(Error::InternalInvariant);
        }

        let AdvicePrefix {
            values: advice_values,
            blinds: advice_blinds,
            theta,
        } = advice;
        let LookupPrefix {
            lookups,
            // The shared compressed tables are dead after the product stage.
            compressed_tables: _,
            beta,
            gamma,
        } = lookup;

        let fixed_cosets =
            core::array::from_fn(|column| target.fixed_polynomials().cosets().column(column));
        let sigma_cosets =
            core::array::from_fn(|column| target.sigma_polynomials().cosets().column(column));
        let mut staged_columns = Vec::with_capacity(action_count + action_count * ADVICE_COLUMNS);
        // The sparse instance inputs are the statement records themselves,
        // read by index from the shared record slice: no prefix is copied out
        // of the dense columns.
        staged_columns.extend(action_range.map(|index| {
            (
                index,
                LagrangeFormInput::SparseInstance {
                    statements: Arc::clone(&self.statements),
                    index,
                },
            )
        }));
        // The advice columns are uniquely owned here: the advice stage's
        // commitment tasks have released them, so recovery must not copy.
        for (action, columns) in advice_values.into_iter().enumerate() {
            for column in columns {
                let column = column.into_unique().ok_or(Error::InternalInvariant)?;
                staged_columns.push((action, LagrangeFormInput::Dense(column)));
            }
        }
        // The permuted lookup columns are staged before the transforms run:
        // they, the instance/advice columns, and the fixed-only table
        // compression are independent once `theta` is known. Their completed
        // residues release fold tasks in the shared quotient coordinator.
        let lookup_count = target.lookups().len();
        let mut staged_permuted = Vec::with_capacity(action_count * lookup_count * 2);
        let mut lookup_blinds = Vec::with_capacity(action_count);
        for (action, action_lookups) in lookups.into_iter().enumerate() {
            let mut action_lookups = action_lookups.into_iter();
            let action_blinds: [_; fold_order::LOOKUP_COUNT] = try_array_from_fn(|_| {
                let permuted = action_lookups.next().ok_or(Error::InternalInvariant)?;
                // The permuted columns transfer into the form transforms as
                // their sole owners (the product stage released its handles),
                // so recovery must not copy; the compressed input column is
                // dead after the product stage and drops here.
                staged_permuted.push((
                    action,
                    permuted
                        .permuted_input
                        .into_unique()
                        .ok_or(Error::InternalInvariant)?,
                ));
                staged_permuted.push((
                    action,
                    permuted
                        .permuted_table
                        .into_unique()
                        .ok_or(Error::InternalInvariant)?,
                ));
                Ok((permuted.input_blind, permuted.table_blind))
            })?;
            lookup_blinds.push(action_blinds);
        }
        // Inventory tie: two permuted-column transforms per (Action, lookup).
        if staged_permuted.len() != quotient_stage::permuted_transforms(action_count) {
            return Err(Error::InternalInvariant);
        }
        // Input sides compress per Action. Identical ordered fixed-table
        // tuples share one compression across both lookups and Actions.
        let table_sources = target.lookup_preparation().sources();
        if table_sources.len() != lookup_count {
            return Err(Error::InternalInvariant);
        }
        let inputs = staged_columns
            .into_iter()
            .map(|(_, input)| input)
            .chain(
                staged_permuted
                    .into_iter()
                    .map(|(_, values)| LagrangeFormInput::Dense4N(values)),
            )
            .collect();
        // Validate the shape once. Each residue binds its completed columns
        // before any fold task can read these placeholders.
        let instance_cosets = vec![ExtendedCoset::pending(); action_count];
        let advice_cosets = vec![vec![ExtendedCoset::pending(); ADVICE_COLUMNS]; action_count];
        let lookup_cosets = vec![
            core::array::from_fn(|_| LookupCosets {
                compressed_table: Arc::new(ExtendedCoset::pending()),
                permuted_input: ExtendedCoset::pending(),
                permuted_table: ExtendedCoset::pending(),
            });
            action_count
        ];

        let beta_deltas = core::array::from_fn(|column| {
            beta.mul(&target.permutation_identities().deltas()[column])
        });

        // Degree-classed fold over one fused row pass: every complete
        // constraint is divisible by `Z_H`, so a
        // total-degree-`d` term's quotient contribution is determined by its
        // values on the rotation-closed stride-`8N/M_d` view of the extended
        // coset (`M_d = N·2^⌈log₂(d−1)⌉`). A single pass computes each row's
        // complete protocol-order Horner chain — the 8N terms jumping the
        // carved slots with precomputed y-power steps, the N/2N/4N terms
        // folding into per-class accumulators under their slots' absolute
        // y-powers, which reproduces the same field elements because field
        // addition is associative — and divides every accumulator by its
        // constant per-sub-coset vanishing value as the row leaves the
        // pass. The frozen per-action slot order is: the gate constraints,
        // then permutation l_0 / l_last / continuity / set rules, then per
        // lookup l_0 / l_last / product rule / permuted l_0 / permuted
        // continuity.
        // The lookup rules' degree-4 left branches additionally fold on 4N.
        // They are not individually divisible by Z_H: run::correct_lookup
        // converts their modular quotients to the 8N representation before
        // adding them to the other classes' coefficients.
        let y = &vanishing.y;
        // The slot geometry is the frozen fold order's; the runtime shape must
        // match the description it was derived from.
        if permutation_set_count != fold_order::PERMUTATION_SET_COUNT
            || lookup_count != fold_order::LOOKUP_COUNT
        {
            return Err(Error::InternalInvariant);
        }
        let terms_per_action = fold_order::TERMS_PER_ACTION;
        let total_terms = terms_per_action * action_count;
        // The fold plans share the proof-specific coset inputs; fixed and
        // sigma cosets remain borrowed from the target. Product cosets move
        // out of the retained stage records here (they are quotient-stage
        // temporaries). Residue plans share these product inputs until their
        // final fold reader returns, independently of the class inverses.
        // The product records end here: their cosets go to the fold, their
        // coefficients and blinds become openings on the returned prefix.
        let (permutation_openings, permutation_cosets) =
            split_product_openings(permutations.products, |product| {
                let (opening, coset) = product.forms.into_opening(product.blind)?;
                let coset = coset.expand(&opening.coefficients, target.fft(), self.execution)?;
                Ok((opening, coset))
            })?;
        let (lookup_product_openings, lookup_product_cosets) =
            split_product_openings(lookup_products.products, |product| {
                let (opening, coset) = product.forms.into_opening(product.blind)?;
                let coset = coset.expand(&opening.coefficients, target.fft(), self.execution)?;
                Ok((opening, coset))
            })?;
        // Each product's coset arrives on the class its consumers require
        // (`fold_order::permutation_product_class`): the kept permutation
        // sets and the lookup products on the extended coset, the singleton
        // permutation set on the 2N class coset the fold reads at stride 4.
        let permutation_cosets = permutation_cosets
            .into_iter()
            .map(ActionPermutationCosets::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        let lookup_product_cosets = lookup_product_cosets
            .into_iter()
            .map(extended_products)
            .collect::<Result<Vec<_>, _>>()?;
        let base = build_fold_plan(
            target,
            FoldInputs {
                advice_cosets,
                instance_cosets,
                lookup_cosets,
                common: Arc::new(FoldCommon {
                    fixed_cosets,
                    sigma_cosets,
                    permutation_cosets,
                    lookup_product_cosets,
                    beta,
                    gamma,
                    beta_deltas,
                    y: *y,
                    theta,
                    total_terms,
                    terms_per_action,
                }),
            },
            SmallClassSlots::FROZEN,
            self.execution,
        )?;
        if ipa_mask.alphas.len() != K as usize {
            return Err(Error::InternalInvariant);
        }
        let output = run::execute(
            target,
            &mut self.workspace.msm,
            &mut self.workspace.fft,
            self.execution,
            inputs,
            base,
            theta,
            commit,
            piece_blinds,
            ipa_mask,
            #[cfg(test)]
            &mut timing,
        )?;
        let mut columns = output.columns.into_iter();
        let advice_coefficients = (0..action_count)
            .map(|_| columns.by_ref().take(ADVICE_COLUMNS).collect())
            .collect();
        let mut permuted_lookup_coefficients = Vec::with_capacity(action_count);
        for action_blinds in lookup_blinds {
            let mut action_blinds = action_blinds.into_iter();
            let action = try_array_from_fn(|_| {
                let (input_blind, table_blind) =
                    action_blinds.next().ok_or(Error::InternalInvariant)?;
                Ok(PermutedLookupCoefficients {
                    input: columns.next().ok_or(Error::InternalInvariant)?,
                    table: columns.next().ok_or(Error::InternalInvariant)?,
                    input_blind,
                    table_blind,
                })
            })?;
            permuted_lookup_coefficients.push(action);
        }
        if columns.next().is_some() {
            return Err(Error::InternalInvariant);
        }
        #[cfg(test)]
        {
            timing.mark(crate::native::stage_timing::QuotientStage::PieceCommitments);
            timing.finish();
        }
        Ok(PreparedQuotient {
            pieces: output.pieces,
            commitments: output.commitments,
            mask: output.mask,
            advice_coefficients,
            advice_blinds,
            permuted_lookup_coefficients,
            permutation_openings,
            lookup_product_openings,
        })
    }

    /// Constructs the quotient pieces, commits them, and squeezes `x`.
    ///
    /// Consumes the advice, lookup, and both product-stage records; the
    /// vanishing record is borrowed. Advice and permuted-lookup Lagrange
    /// buffers transfer into the form transforms instead of being cloned.
    /// Their coefficient forms, product coefficients, and opening blinds
    /// survive into the returned prefix. Proof-specific cosets are temporary
    /// to each window. Fixed and sigma cosets are borrowed from shared target
    /// preparation, computed and retained on the heap by the current `WarmUp`
    /// settings of [`crate::tuning::FIXED_COSETS`] and
    /// [`crate::tuning::SIGMA_COSETS`].
    /// At most [`crate::sizing::ACTION_WINDOW`] Actions expand at once. Opening
    /// coefficients remain live for all Actions, so total memory is still
    /// proportional to the request size.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** `y` from the [`VanishingPrefix`], and through the
    ///   records it consumes the earlier `θ` (compressed lookup columns),
    ///   `β`, and `γ` (product constraints); no other challenge.
    /// - **Publishes** the `QUOTIENT_PIECES` piece commitments in piece
    ///   order (ascending coefficient chunk of the quotient), from one
    ///   coefficient-basis commitment batch.
    /// - **Squeezes** `x`, the evaluation point, carried on the returned
    ///   [`QuotientPrefix`].
    /// - **Draws** no randomness: the piece blinds arrive pre-sampled, one
    ///   per piece in piece order.
    ///
    /// Everything before the piece commitments — the form transforms, the
    /// extended-coset constraint fold, the vanishing division, and the
    /// class interpolation — is preparation: a mathematical dependency on
    /// the challenges above and the committed columns, free to run in any
    /// task order. The piece write loop is the only transcript-ordered
    /// section and follows the batch's job order.
    ///
    /// Logical work and buffer counts are defined in [`quotient_stage`]. Form
    /// transforms, lookup-table compression, and interpolation run per window.
    /// A single window can commit each finished piece immediately; multiple
    /// windows first combine their weighted, unblinded coefficients, then
    /// commit each final piece once. The loop below explains the window weights.
    #[allow(clippy::too_many_arguments)] // stage prefixes and pre-sampled randomness stay separate
    pub(crate) fn construct_quotient(
        &mut self,
        advice: AdvicePrefix,
        lookup: LookupPrefix,
        permutations: PermutationPrefix,
        lookup_products: LookupProductPrefix,
        vanishing: &VanishingPrefix,
        piece_blinds: [Fp; QUOTIENT_PIECES],
        ipa_mask: IpaMaskRandomness,
    ) -> Result<QuotientPrefix, Error> {
        let count = self.action_count();
        let mut prepared = if count <= crate::sizing::ACTION_WINDOW {
            self.prepare_quotient_window(
                advice,
                lookup,
                permutations,
                lookup_products,
                vanishing,
                0..count,
                true,
                &piece_blinds,
                &ipa_mask,
            )?
        } else {
            let AdvicePrefix {
                values,
                blinds,
                theta,
            } = advice;
            let LookupPrefix {
                lookups,
                compressed_tables,
                beta,
                gamma,
            } = lookup;
            let mut values = values.into_iter();
            let mut blinds = blinds.into_iter();
            let mut lookups = lookups.into_iter();
            let mut permutations = permutations.products.into_iter();
            let mut products = lookup_products.products.into_iter();
            // This shared table is no longer read after product construction.
            drop(compressed_tables);
            let mut result = PreparedQuotient::empty(self.execution);
            for start in (0..count).step_by(crate::sizing::ACTION_WINDOW) {
                let end = (start + crate::sizing::ACTION_WINDOW).min(count);
                let len = end - start;
                let window = self.prepare_quotient_window(
                    AdvicePrefix {
                        values: values.by_ref().take(len).collect(),
                        blinds: blinds.by_ref().take(len).collect(),
                        theta,
                    },
                    LookupPrefix {
                        lookups: lookups.by_ref().take(len).collect(),
                        compressed_tables: core::array::from_fn(|_| SharedPoly::new(Vec::new())),
                        beta,
                        gamma,
                    },
                    PermutationPrefix {
                        products: permutations.by_ref().take(len).collect(),
                    },
                    LookupProductPrefix {
                        products: products.by_ref().take(len).collect(),
                    },
                    vanishing,
                    start..end,
                    false,
                    &piece_blinds,
                    &ipa_mask,
                )?;
                // Let T = TERMS_PER_ACTION and y = vanishing.y, the constraint
                // folding challenge. Local Action i in this len-Action window
                // has outer Horner weight y^(T*(len-1-i)); its global index is
                // start+i. Multiplying by y^(T*(count-end)), with end=start+len,
                // gives y^(T*(count-1-start-i)), its weight in the full fold.
                // This also scales fixed-only terms and lookup remainders.
                // Interpolation and remainder correction are linear, so sums
                // can be formed in coefficient space before the sole blinding,
                // commitment, and transcript-write stage.
                let exponent = (fold_order::TERMS_PER_ACTION * (count - end)) as u64;
                result.add_window(window, vanishing.y.pow_u64(exponent));
            }
            result
        };
        const _: () = assert!(quotient_stage::QUOTIENT_COEFFICIENTS == QUOTIENT_PIECES * N);
        let mut pieces: Vec<_> = prepared
            .pieces
            .into_iter()
            .zip(piece_blinds)
            .map(|(coefficients, blind)| QuotientPiece {
                coefficients: SharedPoly::new(coefficients),
                blind,
                commitment: VestaPoint::IDENTITY,
            })
            .collect();
        if count > crate::sizing::ACTION_WINDOW {
            let jobs: Vec<_> = pieces
                .iter()
                .map(|piece| (&piece.coefficients, &piece.blind))
                .collect();
            // Interpolation produced the fixed-size pieces; mask indices are
            // protocol constants. Rejection breaks those prepared MSM shapes.
            let (commitments, mask) = self
                .target
                .parameters()
                .commit_coefficients_batch_with_sparse_projective(
                    &jobs,
                    crate::native::storage::Column::from(&IPA_MASK_GENERATOR_INDICES[..]),
                    Arc::new(ipa_mask.alphas.to_vec()),
                    &ipa_mask.blind,
                    &mut self.workspace.msm,
                    self.execution,
                )
                .map_err(|_| Error::InternalInvariant)?;
            prepared.commitments = commitments;
            prepared.mask = mask;
        }
        let normalized = normalized(&prepared.commitments);
        if normalized.len() != pieces.len() {
            return Err(Error::InternalInvariant);
        }
        // Piece blinds are sampled for this attempt; an identity cannot be
        // emitted and requires new proof randomness.
        for (piece, commitment) in pieces.iter_mut().zip(normalized) {
            piece.commitment = commitment;
            self.transcript
                .write_point(&piece.commitment)
                .map_err(|_| Error::RetryRandomness)?;
        }
        let x = self.transcript.squeeze_challenge();
        Ok(QuotientPrefix {
            pieces,
            advice_coefficients: prepared.advice_coefficients,
            advice_blinds: prepared.advice_blinds,
            permuted_lookup_coefficients: prepared.permuted_lookup_coefficients,
            permutation_openings: prepared.permutation_openings,
            lookup_product_openings: prepared.lookup_product_openings,
            ipa_mask: IpaMaskEarly {
                commitment: prepared.mask,
                alphas: ipa_mask.alphas,
                blind: ipa_mask.blind,
            },
            x,
        })
    }
}

/// Full-width permutation chunks per Action: every chunk but the trailing
/// singleton, whose degree-3 rule folds on the 2N class instead.
pub(super) const KEPT_PERMUTATION_SETS: usize = PERMUTATION_COLUMN_COUNT / PERMUTATION_CHUNK_LEN;

/// Rows a fold task gathers at a time into its row-major frame blocks:
/// the group's rows plus one rotation neighbour on each side.
pub(super) const FRAME_GROUP_ROWS: usize = 4;
/// Layout of one Action's gathered row: ten unique advice columns and the
/// instance column, each lookup's permuted-input / permuted-table /
/// compressed-table cosets, the kept grand products and lookup grand products.
const GATHER_LOOKUP_BASE: usize = ADVICE_COLUMNS + 1;
const GATHER_KEPT_PRODUCT_BASE: usize = GATHER_LOOKUP_BASE + 3 * fold_order::LOOKUP_COUNT;
const GATHER_LOOKUP_PRODUCT_BASE: usize = GATHER_KEPT_PRODUCT_BASE + KEPT_PERMUTATION_SETS;
pub(super) const GATHER_WIDTH: usize = GATHER_LOOKUP_PRODUCT_BASE + fold_order::LOOKUP_COUNT;
/// The shared gathered row: the kept sets' sigma columns and the singleton
/// set's sigma column.
pub(super) const SIGMA_GATHER_WIDTH: usize = FIXED_FACTOR_COLUMNS + 1;

const _: () = {
    // The fold's split of the permutation products matches the consumer
    // census the product stage produced the cosets from: the kept sets are
    // read on the fused 8N pass, the singleton only on the 2N class.
    assert!(KEPT_PERMUTATION_SETS + 1 == fold_order::PERMUTATION_SET_COUNT);
    let mut set = 0;
    while set < KEPT_PERMUTATION_SETS {
        assert!(matches!(
            fold_order::permutation_product_class(set),
            fold_order::DegreeClass::Extended
        ));
        set += 1;
    }
    assert!(matches!(
        fold_order::permutation_product_class(KEPT_PERMUTATION_SETS),
        fold_order::DegreeClass::Class2N
    ));
};

/// One Action's permutation grand-product cosets as the fold owns them: the
/// kept (full-width) sets on the extended coset and the singleton set on the
/// 2N class coset.
#[derive(Clone)]
struct ActionPermutationCosets {
    kept: [ExtendedCoset; KEPT_PERMUTATION_SETS],
    singleton: Class2NCoset,
}

impl TryFrom<[ProductCoset; fold_order::PERMUTATION_SET_COUNT]> for ActionPermutationCosets {
    type Error = Error;

    fn try_from(cosets: [ProductCoset; fold_order::PERMUTATION_SET_COUNT]) -> Result<Self, Error> {
        let mut cosets = cosets.into_iter();
        let mut kept = Vec::with_capacity(KEPT_PERMUTATION_SETS);
        for _ in 0..KEPT_PERMUTATION_SETS {
            kept.push(
                cosets
                    .next()
                    .ok_or(Error::InternalInvariant)?
                    .into_extended()?,
            );
        }
        let singleton = cosets
            .next()
            .ok_or(Error::InternalInvariant)?
            .into_class_2n()?;
        if cosets.next().is_some() {
            return Err(Error::InternalInvariant);
        }
        Ok(Self {
            kept: kept.try_into().map_err(|_| Error::InternalInvariant)?,
            singleton,
        })
    }
}

/// Every product of one Action on the extended coset (the lookup products).
fn extended_products<const PER_ACTION: usize>(
    cosets: [ProductCoset; PER_ACTION],
) -> Result<[ExtendedCoset; PER_ACTION], Error> {
    let mut extended = Vec::with_capacity(PER_ACTION);
    for coset in cosets {
        extended.push(coset.into_extended()?);
    }
    extended.try_into().map_err(|_| Error::InternalInvariant)
}

/// Columns across the kept sets: the per-row fixed-factor offsets are one
/// entry each.
const FIXED_FACTOR_COLUMNS: usize = KEPT_PERMUTATION_SETS * PERMUTATION_CHUNK_LEN;

/// Where one fold column lives among the shared inputs, resolved and
/// validated once per proof so row tasks can index straight to the slice.
#[derive(Clone, Copy)]
enum FoldColumnSource {
    Fixed(usize),
    Advice(usize),
    Instance,
}

/// One Action's validated fold descriptors and challenge weights, built once
/// per proof in [`plan`]; row tasks in [`rows`] resolve borrowed views from
/// these without allocation or metadata work.
struct ActionPlan {
    query_sources: [FoldColumnSource; GATE_QUERY_COUNT],
    query_rotations: [usize; GATE_QUERY_COUNT],
    kept_sets: [KeptSetPlan; KEPT_PERMUTATION_SETS],
    set_2_source: FoldColumnSource,
    gate_powers_2n: [Fp; generated_expressions::GATE_PROGRAMS_2N.len()],
    gate_curve_powers_4n: [Fp; 2],
    perm_l_0_power: Fp,
    perm_l_last_power: Fp,
    set_2_rule_power: Fp,
    continuity_powers: [Fp; fold_order::PERMUTATION_SET_COUNT - 1],
    lookup_l_0_powers: [Fp; fold_order::LOOKUP_COUNT],
    lookup_l_last_powers: [Fp; fold_order::LOOKUP_COUNT],
    lookup_permuted_l_0_powers: [Fp; fold_order::LOOKUP_COUNT],
    lookup_continuity_powers: [Fp; fold_order::LOOKUP_COUNT],
}

/// One kept permutation set's column sources and the sigma / `β·δⁱ` ranges
/// it reads.
#[derive(Clone, Copy)]
struct KeptSetPlan {
    set_index: usize,
    columns: [FoldColumnSource; PERMUTATION_CHUNK_LEN],
    first_column: usize,
}

/// Completed columns for one residue; shared proof inputs stay in `common`.
struct FoldInputs<'a> {
    advice_cosets: Vec<Vec<ExtendedCoset>>,
    instance_cosets: Vec<ExtendedCoset>,
    lookup_cosets: Vec<[LookupCosets; fold_order::LOOKUP_COUNT]>,
    common: Arc<FoldCommon<'a>>,
}

/// Products, borrowed prepared columns, and challenges shared by all residues.
struct FoldCommon<'a> {
    fixed_cosets: [FpCosetView<'a>; FIXED_COLUMNS],
    sigma_cosets: [FpCosetView<'a>; PERMUTATION_COLUMN_COUNT],
    permutation_cosets: Vec<ActionPermutationCosets>,
    lookup_product_cosets: Vec<[ExtendedCoset; fold_order::LOOKUP_COUNT]>,
    beta: Fp,
    gamma: Fp,
    beta_deltas: [Fp; PERMUTATION_COLUMN_COUNT],
    y: Fp,
    theta: Fp,
    total_terms: usize,
    terms_per_action: usize,
}

impl<'a> core::ops::Deref for FoldInputs<'a> {
    type Target = FoldCommon<'a>;
    fn deref(&self) -> &Self::Target {
        &self.common
    }
}

/// Per-proof constants of the fold, derived once and shared by every task.
struct FoldConstants<'a> {
    set_2_column: &'a PermutationColumn,
    set_2_sigma: FpCosetView<'a>,
    set_2_beta_delta: Fp,
    y_ladder: Buffer<Fp>,
    y_powers: [Fp; generated_expressions::MAX_GATE_CONSTRAINTS + 1],
    gate_challenge_coefficients: generated_expressions::GateChallengeCoefficients,
    gate_coefficients_4n: generated_expressions::Gate4NCoefficients,
    /// For the shared affine gate pass: each Action's gate-block weight
    /// `y^(215·(A−1−a))`, their sum, the in-block powers `y^(192−i)`, and the
    /// rule-block offset `y^22` (the gates precede 22 rule slots per Action).
    action_weights: Buffer<Fp>,
    weight_sum: Fp,
    /// The absolute in-Action power of every gate slot,
    /// `y^(TERMS_PER_ACTION − 1 − i)`: the weight a gate constraint carries
    /// within its Action's block, including the offset of the 22 rule slots
    /// that follow the gates. The row fold accumulates every 8N term under
    /// these powers in one product sum per Action and combines the Action
    /// blocks by `y_action_step`.
    slot_powers: [Fp; generated_expressions::GATE_CONSTRAINT_COUNT],
    /// The absolute in-Action powers of the kept sets' product rules and of
    /// the lookup product rules — the 8N rules the row fold accumulates.
    rule_powers: [Fp; KEPT_PERMUTATION_SETS],
    lookup_rule_powers: [Fp; fold_order::LOOKUP_COUNT],
    /// `y^TERMS_PER_ACTION`, the step between consecutive Actions' finished
    /// row values.
    y_action_step: Fp,
    scale_8n: [Fp; 8],
    scale_4n: [Fp; 4],
    scale_2n: [Fp; 2],
    scale_n: Fp,
    /// The lookup input kernels the fold evaluates at each row, with the
    /// θ-derived and expression constants they read.
    lookup_input_kernels: [LookupInputRowKernel; fold_order::LOOKUP_COUNT],
    theta: ThetaConstants,
    lookup_constants: LookupKernelConstants,
}

/// The shared state of one quotient fold; every row-chunk task holds an
/// `Arc` to it and rebuilds its per-action views (a few dozen slice
/// references) from the owned inputs.
struct FoldPlan<'a> {
    target: &'a FixedTarget,
    inputs: FoldInputs<'a>,
    constants: Arc<FoldConstants<'a>>,
    /// Validated per-Action descriptors and challenge weights, built once
    /// from the inputs, constants, and the fold order's slot positions.
    action_plans: Arc<Vec<ActionPlan>>,
}

/// One residue-major window of the extended domain a fold task owns: rows
/// `residue + 8k` for `k` in `k_offset..k_offset + FOLD_CHUNK_ROWS`. Every
/// dynamic and static coset is stored residue-major, so a window's reads —
/// and its `±8`-row rotations — are contiguous within one residue tile.
#[derive(Clone, Copy, Debug)]
pub(super) struct FoldWindow {
    pub(super) residue: usize,
    pub(super) k_offset: usize,
}

impl FoldWindow {
    /// The extended row at `offset` into the window.
    #[inline(always)]
    pub(super) fn row(&self, offset: usize) -> usize {
        self.residue + ((self.k_offset + offset) << EXTENDED_ROTATION_STRIDE.trailing_zeros())
    }
}
