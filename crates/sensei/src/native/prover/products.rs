//! Permutation and lookup grand products, followed by the vanishing mask.
//!
//! Product commitments share a batch with coefficient preparation. Cosets are
//! prepared here for a single-window proof or deferred to their quotient window.
//! Transcript writes follow Action and argument order independently of scheduling.
//! Construction lives in [`permutation`] and [`lookup`], sharing the exclusive
//! grand-product [`walk`]; this module owns the commitment and installation order.

mod lookup;
mod permutation;
mod walk;

use lookup::prepare_certified_lookup_product;
#[cfg(test)]
use lookup::prepare_lookup_product;
pub(super) use permutation::{permutation_column_values, prepare_permutation_products};
#[cfg(test)]
pub(super) use walk::batch_invert_groups;
pub(super) use walk::two_lane_exclusive_walk;

use crate::native::try_array_from_fn;

use crate::Error;
use crate::native::commitment::normalized;
use crate::native::generated_expressions;
use crate::native::randomness::{
    LOOKUPS_PER_ACTION, PERMUTATION_SETS_PER_ACTION, PermutationBlinding, ProductBlinding,
    VanishingRandomness,
};
use crate::native::target::{
    ADVICE_COLUMNS, BLINDING_FACTORS, LagrangeCommitScalars, N, PERMUTATION_CHUNK_LEN,
    PERMUTATION_SETS,
};
#[cfg(test)]
use crate::native::{curve::VestaPoint, field::Fp, polynomial::SharedPoly};
use alloc::vec::Vec;

#[cfg(test)]
use super::PermutedLookup;
use super::inventory::product_stage;
use super::{
    AdvicePrefix, LookupPrefix, LookupProductPrefix, PermutationPrefix, ProductForms,
    ProductPolynomialForms, ProverPrefix, VanishingPrefix, fold_order,
    owned_lagrange_to_product_forms,
};

impl ProverPrefix<'_> {
    /// Constructs and commits the permutation and lookup grand products.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** the challenges `β` and `γ`, squeezed at the end of
    ///   [`Self::commit_lookup_permutations`] and carried on the
    ///   [`LookupPrefix`]; no other challenge is read.
    /// - **Publishes**, in this order: every Action's permutation
    ///   grand-product commitments (Action-major, then set index ascending,
    ///   `PERMUTATION_SETS` per Action), then every Action's lookup
    ///   grand-product commitments (Action-major, then lookup index
    ///   ascending). No challenge intervenes between the two families, which
    ///   is what lets one commitment batch serve both.
    /// - **Squeezes** nothing: the next challenge, `y`, belongs to
    ///   [`Self::commit_vanishing_random_polynomial`].
    /// - **Draws** no randomness: the set and product blindings arrive
    ///   pre-sampled from the up-front schedule and are only installed here.
    ///
    /// Everything before the final loop is preparation — a mathematical
    /// dependency on `β`, `γ`, the advice, the instance columns, and the
    /// compressed tables, free to run in any task order — and the final loop
    /// is the only transcript-ordered section: it walks the prepared records
    /// in the order above, independent of which tasks finished first.
    ///
    /// # Work and buffer inventory
    ///
    /// Logical counts, in field elements, from [`product_stage`]; per Action
    /// the stage builds [`product_stage::PRODUCTS_PER_ACTION`] products.
    ///
    /// - **Permutation set** (`PERMUTATION_SETS` per Action): one pass over
    ///   the set's value columns (advice or instance, `N` rows each, up to
    ///   `PERMUTATION_CHUNK_LEN` of them), their sigma columns, and the
    ///   identity columns; one batch inversion over the set's *active* rows
    ///   only (the sparse assignment schedule), a running-product scan
    ///   filling rows through `USABLE_ROWS_END`, then `BLINDING_FACTORS`
    ///   pre-sampled mask rows; a second wave rescales later sets' usable
    ///   rows by the preceding sets' final states.
    /// - **Lookup product** (`LOOKUPS.len()` per Action): one pass over the
    ///   compressed input, permuted input, permuted table, and shared
    ///   compressed table (`N` rows each); one inversion of the denominator
    ///   prefix product with a backward walk (no batch inversion); then the
    ///   mask rows.
    /// - **Per product, shared by both families:** one copy of the `N`-row
    ///   Lagrange column into the commitment batch's side job
    ///   ([`product_stage::STAGED_COPY_PER_PRODUCT`]), one `N`-scalar
    ///   Lagrange-basis commitment, one base inverse transform (`N`), and one
    ///   expansion to the product's class coset — `EXTENDED_N` values, or the
    ///   `2N` class coset for the singleton permutation set, whose every fold
    ///   consumer is a 2N or N term ([`product_stage::COSET_PER_SINGLETON_PRODUCT`])
    ///   — inverse transforms run alongside the commitment work. When the
    ///   proof fits one quotient window, expansions also run here; otherwise
    ///   they run when each quotient window starts.
    /// - **Alive at return, per Action:** `N` coefficients per product, plus
    ///   class cosets for single-window proofs. [`product_stage::RETAINED_PER_ACTION`]
    ///   counts that expanded case. The quotient fold releases cosets after
    ///   their last reader; coefficients survive for the openings.
    ///
    /// All product denominators for one action are inverted together, while
    /// commitment and transcript order remains permutation-first.
    pub(crate) fn commit_product_arguments(
        &mut self,
        advice: &AdvicePrefix,
        lookup: &LookupPrefix,
        permutation_blindings: Vec<[PermutationBlinding; PERMUTATION_SETS_PER_ACTION]>,
        lookup_blindings: Vec<[ProductBlinding; LOOKUPS_PER_ACTION]>,
    ) -> Result<(PermutationPrefix, LookupProductPrefix), Error> {
        let target = self.target;
        if advice.values.len() != self.instance_polynomials.len()
            || lookup.lookups.len() != advice.values.len()
            || advice.values.iter().any(|columns| {
                columns.len() != ADVICE_COLUMNS || columns.iter().any(|column| column.len() != N)
            })
            || self
                .instance_polynomials
                .iter()
                .any(|column| column.len() != N)
            || target.sigma_values().iter().any(|column| column.len() != N)
            || target.permutation_identities().values().len() != target.permutation_columns().len()
            || target
                .permutation_identities()
                .values()
                .iter()
                .any(|column| column.len() != N)
        {
            return Err(Error::InternalInvariant);
        }

        let set_count = target
            .permutation_columns()
            .len()
            .div_ceil(PERMUTATION_CHUNK_LEN);
        // The inventory's per-Action counts are the runtime shape.
        if set_count != PERMUTATION_SETS
            || target.lookups().len() != generated_expressions::LOOKUPS.len()
            || target.sigma_values().len() != target.permutation_columns().len()
        {
            return Err(Error::InternalInvariant);
        }

        // Shape-check the pre-sampled set blindings: one per permutation
        // chunk per action, each masking `BLINDING_FACTORS` tail rows.
        if permutation_blindings.len() != advice.values.len()
            || permutation_blindings.iter().any(|action_blindings| {
                action_blindings.len() != set_count
                    || action_blindings
                        .iter()
                        .any(|blinding| blinding.rows.len() != BLINDING_FACTORS)
            })
        {
            return Err(Error::InternalInvariant);
        }

        if lookup
            .lookups
            .iter()
            .any(|lookups| lookups.len() != target.lookups().len())
            || lookup.compressed_tables.len() != target.lookups().len()
            || lookup
                .compressed_tables
                .iter()
                .any(|table| table.len() != N)
        {
            return Err(Error::InternalInvariant);
        }

        let (beta, gamma) = (lookup.beta, lookup.gamma);
        let prepare = || {
            prepare_permutation_products(
                target,
                &advice.values,
                &self.instance_polynomials,
                permutation_blindings,
                &beta,
                &gamma,
                set_count,
                self.execution,
            )
        };
        #[cfg(test)]
        let mut prepared_permutations =
            crate::native::stage_timing::measure_product_prepare(prepare)?;
        #[cfg(not(test))]
        let mut prepared_permutations = prepare()?;
        // Shape-check the pre-sampled product blindings: one per lookup per
        // action, each masking `BLINDING_FACTORS` tail rows.
        if lookup_blindings.len() != lookup.lookups.len()
            || lookup_blindings.iter().any(|action_blindings| {
                action_blindings
                    .iter()
                    .any(|blinding| blinding.rows.len() != BLINDING_FACTORS)
            })
        {
            return Err(Error::InternalInvariant);
        }

        let mut lookup_jobs =
            Vec::with_capacity(lookup.lookups.iter().map(|action| action.len()).sum());
        for (action, (action_lookups, action_blindings)) in
            lookup.lookups.iter().zip(lookup_blindings).enumerate()
        {
            if action_lookups.len() != action_blindings.len() {
                return Err(Error::InternalInvariant);
            }
            lookup_jobs.extend(
                lookup
                    .certified_product_inputs(action)?
                    .zip(action_blindings)
                    .map(|job| (action, job)),
            );
        }
        // Outputs outlive every job; each running job can also hold its
        // denominators and zero-preserving inversion scratch.
        self.execution.provision(
            N,
            lookup_jobs.len() + 2 * lookup_jobs.len().min(self.execution.budget.get()),
        );
        let prepared_products =
            self.execution
                .map(lookup_jobs, move |(_action, job), execution| {
                    let (input, blinding) = job;
                    prepare_certified_lookup_product(&input, blinding, &beta, &gamma, execution)
                });
        let mut prepared_products = prepared_products
            .into_iter()
            .collect::<Result<Vec<_>, Error>>()?
            .into_iter();
        let mut prepared_lookups = Vec::with_capacity(lookup.lookups.len());
        for _ in &lookup.lookups {
            let action_products: [_; LOOKUPS_PER_ACTION] =
                try_array_from_fn(|_| prepared_products.next().ok_or(Error::InternalInvariant))?;
            prepared_lookups.push(action_products);
        }
        if prepared_products.next().is_some() {
            return Err(Error::InternalInvariant);
        }
        // One commitment task group for both product families: the
        // permutation products' commitments precede the lookup products' in
        // the transcript and no challenge intervenes, so a single batch — one
        // set of transform side jobs, one normalization — commits them in
        // that order. Cloned rows become form side jobs inside the
        // commitment scope, so otherwise-idle MSM workers can overlap the
        // independent transforms.
        let permutation_count = prepared_permutations
            .iter()
            .map(|products| products.len())
            .sum::<usize>();
        // Each product's transform side job carries the class its coset is
        // produced on: the fold reads the singleton permutation set only on
        // the 2N and N classes, so its coset is the 2N class coset (the
        // extended coset's stride-4 rows); every other product folds on the
        // fused 8N pass.
        // One staged form per product; the `flat_map`s hide the exact bound
        // from a collect, so the buffer is sized and filled fallibly by hand.
        let lookup_count = prepared_lookups
            .iter()
            .map(|products| products.len())
            .sum::<usize>();
        let mut staged_forms = Vec::with_capacity(permutation_count + lookup_count);
        for (action, products) in prepared_permutations.iter().enumerate() {
            for (set, product) in products.iter().enumerate() {
                staged_forms.push((
                    action,
                    (
                        self.execution.copy(product.forms.staged()?),
                        fold_order::permutation_product_class(set),
                    ),
                ));
            }
        }
        for (action, products) in prepared_lookups.iter().enumerate() {
            for product in products {
                staged_forms.push((
                    action,
                    (
                        self.execution.copy(product.forms.staged()?),
                        fold_order::DegreeClass::Extended,
                    ),
                ));
            }
        }
        let staged_forms = staged_forms;
        // Permutation products commit through the prefix-sum interval path
        // (one term per scan run plus the dense tail) and lookup products
        // densely, all in the one mixed batch so job order stays publication
        // order.
        let jobs = prepared_permutations
            .iter()
            .flat_map(|action_products| {
                action_products.iter().map(|product| {
                    let rows = product.forms.staged()?;
                    let scalars = if product.interval_runs.is_empty() {
                        LagrangeCommitScalars::Dense(rows)
                    } else {
                        LagrangeCommitScalars::PiecewiseConstantPrefix {
                            runs: &product.interval_runs,
                            dense: rows,
                        }
                    };
                    Ok((scalars, &product.blind))
                })
            })
            .chain(prepared_lookups.iter().flat_map(|action_products| {
                action_products.iter().map(|product| {
                    Ok((
                        LagrangeCommitScalars::Dense(product.forms.staged()?),
                        &product.blind,
                    ))
                })
            }))
            .collect::<Result<Vec<_>, Error>>()?;
        // Inventory ties: one staged copy and one `N`-row column per product
        // (committed densely or, for an edge-free set, by interval).
        if staged_forms
            .iter()
            .any(|(_, (copy, _))| copy.len() != product_stage::STAGED_COPY_PER_PRODUCT)
            || jobs.iter().any(|(scalars, _)| {
                scalars.dense().len() != product_stage::COMMITMENT_SCALARS_PER_PRODUCT
            })
        {
            return Err(Error::InternalInvariant);
        }
        let deferred = self.action_count() > crate::sizing::ACTION_WINDOW;
        // Product rows and side-job shapes are stage-owned; the batch's error
        // reports their commitment layout, while side-job Results pass through.
        let (pending_commitments, forms) = target
            .parameters()
            .commit_lagrange_mixed_batch_projective_with_side_jobs(
                &jobs,
                staged_forms,
                |(_action, forms), execution| {
                    if deferred {
                        let (mut coefficients, class) = forms;
                        if coefficients.len() != N || !target.fft().ifft(&mut coefficients) {
                            return Err(Error::InternalInvariant);
                        }
                        Ok(ProductPolynomialForms {
                            coefficients,
                            coset: super::ProductCoset::Deferred(class),
                        })
                    } else {
                        owned_lagrange_to_product_forms(forms, target.fft(), execution)
                    }
                },
                &mut self.workspace.msm,
                self.execution,
            )
            .map_err(|_| Error::InternalInvariant)?;
        let forms = forms.into_iter().collect::<Result<Vec<_>, _>>()?;
        if forms.len() != jobs.len()
            || jobs.len() != product_stage::commitment_jobs(advice.values.len())
            || permutation_count > forms.len()
        {
            return Err(Error::InternalInvariant);
        }
        drop(jobs);
        // The permutation products' interval runs were read by the batch's
        // prefix-sum gather alone; they end here instead of riding the product
        // records to quotient entry.
        for product in prepared_permutations.iter_mut().flatten() {
            product.interval_runs = Vec::with_capacity(0);
        }
        let mut forms = forms.into_iter();
        install_staged_product_forms(&mut prepared_permutations, &mut forms, |product| {
            &mut product.forms
        })?;
        install_staged_product_forms(&mut prepared_lookups, &mut forms, |product| {
            &mut product.forms
        })?;

        if forms.next().is_some() {
            return Err(Error::InternalInvariant);
        }

        // Ordered publication (the transcript contract above): permutation
        // products Action-major and set-ascending, then lookup products
        // Action-major and lookup-ascending — the batch's job order.
        // In either loop a blinded identity is a transcript write failure
        // recoverable by fresh proof randomness.
        let mut normalized = normalized(&pending_commitments).into_iter();
        for action_products in &mut prepared_permutations {
            for product in action_products {
                product.commitment = normalized.next().ok_or(Error::InternalInvariant)?;
                self.transcript
                    .write_point(&product.commitment)
                    .map_err(|_| Error::RetryRandomness)?;
            }
        }
        for action_products in &mut prepared_lookups {
            for product in action_products {
                product.commitment = normalized.next().ok_or(Error::InternalInvariant)?;
                self.transcript
                    .write_point(&product.commitment)
                    .map_err(|_| Error::RetryRandomness)?;
            }
        }
        if normalized.next().is_some() {
            return Err(Error::InternalInvariant);
        }

        // This stage is the dense instance columns' last value reader — the
        // quotient stage reads the sparse prefix from the statement records —
        // so their `A·N`-field payload ends here instead of living to the end
        // of the proof. Every later stage takes the Action count from
        // `action_count`, which the statement collection carries.
        self.instance_polynomials = Vec::with_capacity(0);

        Ok((
            PermutationPrefix::new(prepared_permutations),
            LookupProductPrefix::new(prepared_lookups),
        ))
    }
}

impl ProverPrefix<'_> {
    /// Commits to the pre-sampled random polynomial that masks the folded
    /// quotient evaluation, then squeezes the quotient-folding challenge.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** no new challenge; it follows the product commitments
    ///   directly and only checks the product records' shape.
    /// - **Publishes** one commitment: the linear mask `r(X) = r_0 + r_1·X`,
    ///   committed sparsely as its two coefficients (equal to the zero-padded
    ///   dense commitment) with its blind.
    /// - **Squeezes** `y`, the constraint-folding challenge, carried on the
    ///   returned [`VanishingPrefix`] with the mask coefficients.
    /// - **Draws** no randomness: `r_0`, `r_1`, and the blind arrive
    ///   pre-sampled in that order.
    ///
    /// There is no preparation beyond the one sparse commitment; the stage is
    /// entirely transcript-ordered.
    pub(crate) fn commit_vanishing_random_polynomial(
        &mut self,
        permutations: &PermutationPrefix,
        lookups: &LookupProductPrefix,
        randomness: VanishingRandomness,
    ) -> Result<VanishingPrefix, Error> {
        let action_count = self.action_count();
        if permutations.products.len() != action_count || lookups.products.len() != action_count {
            return Err(Error::InternalInvariant);
        }

        // This polynomial is shared by the batch. The pre-sampled linear mask
        // carries the two coefficients of
        // r(X) = r_0 + r_1·X in ascending draw order, followed by its blind:
        // r(X) is revealed at exactly two points of the multi-opening
        // argument, so a linear polynomial preserves the masking role of the
        // earlier dense one. The polynomial is committed, evaluated, and
        // collapsed as its two coefficients: the commitment point and every
        // downstream value equal those of the zero-padded dense form.
        let VanishingRandomness { mask, blind } = randomness;
        let target = self.target;
        // Degrees 0 and 1 fit the fixed coefficient bank; rejection here is a
        // layout failure, distinct from a random identity at the write below.
        let commitment = target
            .parameters()
            .commit_sparse_coefficients(
                &[(0, mask[0]), (1, mask[1])],
                &blind,
                &mut self.workspace.msm,
                self.execution,
            )
            .map_err(|_| Error::InternalInvariant)?;
        // Fresh mask/blind draws can replace a commitment that is identity.
        self.transcript
            .write_point(&commitment)
            .map_err(|_| Error::RetryRandomness)?;
        let y = self.transcript.squeeze_challenge();

        Ok(VanishingPrefix { mask, blind, y })
    }
}

fn install_staged_product_forms<P, const PER_ACTION: usize>(
    actions: &mut [[P; PER_ACTION]],
    forms: &mut impl Iterator<Item = ProductPolynomialForms>,
    forms_of: impl Fn(&mut P) -> &mut ProductForms + Copy,
) -> Result<(), Error> {
    for products in actions.iter_mut() {
        for product in products {
            let form = forms.next().ok_or(Error::InternalInvariant)?;
            // Inventory tie: the forms a product retains are exactly its `N`
            // coefficients and its class coset (`EXTENDED_N` values, or `2N` for
            // the singleton permutation set), validated by the tiled records.
            forms_of(product).install(form)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::{buffer::BufferPool, test_support::reduced_values};

    #[test]
    fn lookup_product_reuses_dirty_scratch_with_zero_denominators() {
        let pool = BufferPool::default();
        pool.provision(N, 3, <Fp>::ONE);
        let inventory = pool.inventory();
        let execution = crate::test_codec::execution().with_buffers(&pool);
        let column = |tag| {
            SharedPoly::new(
                (0..N)
                    .map(|row| <Fp>::from_u64((row + tag) as u64))
                    .collect::<Vec<_>>(),
            )
        };
        let permuted = PermutedLookup {
            compressed_input: column(2),
            permuted_input: column(3),
            permuted_table: column(4),
            input_blind: <Fp>::ZERO,
            table_blind: <Fp>::ZERO,
            input_commitment: VestaPoint::IDENTITY,
            table_commitment: VestaPoint::IDENTITY,
        };
        let table = column(5);
        for zero_at in [
            None,
            Some(0),
            Some(1),
            Some(267),
            Some(N - BLINDING_FACTORS - 1),
            None,
        ] {
            pool.dirty(<Fp>::from_u64(97));
            let beta = zero_at.map_or(<Fp>::ONE, |row| permuted.permuted_input[row].neg());
            let gamma = <Fp>::from_u64(7);
            let blinding = ProductBlinding {
                rows: core::array::from_fn(|row| <Fp>::from_u64((row + 11) as u64)),
                blind: <Fp>::from_u64(13),
            };
            let mut expected = Vec::with_capacity(N);
            let mut state = <Fp>::ONE;
            for row in 0..N - BLINDING_FACTORS {
                expected.push(state);
                let numerator = permuted.compressed_input[row]
                    .add(&beta)
                    .mul(&table[row].add(&gamma));
                let denominator = permuted.permuted_input[row]
                    .add(&beta)
                    .mul(&permuted.permuted_table[row].add(&gamma));
                state = state
                    .mul(&numerator)
                    .mul(&denominator.invert().unwrap_or(<Fp>::ZERO));
            }
            expected.extend_from_slice(&blinding.rows);
            let actual =
                prepare_lookup_product(&permuted, &table, blinding, &beta, &gamma, execution)
                    .unwrap();
            assert_eq!(
                reduced_values(&actual.forms.staged().unwrap()[..]),
                reduced_values(&expected)
            );
            drop(actual);
            assert_eq!(pool.inventory(), inventory);
        }
    }

    #[test]
    fn staged_forms_follow_group_order_and_reject_short_groups() {
        let staged = || {
            core::array::from_fn::<_, 3, _>(|_| {
                ProductForms::staged_rows(vec![<Fp>::ZERO; N]).unwrap()
            })
        };
        let form = |tag| ProductPolynomialForms {
            coefficients: vec![<Fp>::from_u64(tag); N].into(),
            coset: super::super::ProductCoset::Extended(
                super::super::extended_coset_from_dense_rows(vec![
                    <Fp>::ZERO;
                    super::super::EXTENDED_N
                ])
                .unwrap(),
            ),
        };
        let mut first = [staged()];
        let mut second = [staged()];
        let mut forms = (0..6).map(form);
        install_staged_product_forms(&mut first, &mut forms, |product| product).unwrap();
        install_staged_product_forms(&mut second, &mut forms, |product| product).unwrap();
        assert!(forms.next().is_none());
        for (index, product) in first.iter().chain(&second).flatten().enumerate() {
            assert_eq!(
                product.coefficients().unwrap()[0].reduce(),
                <Fp>::from_u64(index as u64).reduce()
            );
        }
        assert!(
            install_staged_product_forms(&mut [staged()], &mut (0..2).map(form), |product| product)
                .is_err()
        );
        assert!(
            install_staged_product_forms(&mut first, &mut (0..3).map(form), |product| product)
                .is_err()
        );
    }
}
