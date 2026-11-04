//! Circuit commitment recipes, normalization, and reusable Udon MSM storage.

#[cfg(feature = "prover")]
use alloc::vec;
use alloc::{sync::Arc, vec::Vec};
use sensei_shared::commitment_tables::{self as tables, Codebook, SrsTable};
#[cfg(all(test, feature = "prover", feature = "verifier"))]
use udon::exec::Executor;
#[cfg(feature = "prover")]
use udon::{exec::TaskBudget, msm::Input};

pub(crate) mod msm;
pub(crate) use msm::MsmWorkspace;

#[cfg(feature = "prover")]
use super::worker::Execution;
#[cfg(feature = "prover")]
use super::{storage::Column, worker::run};
use udon::curve::{
    EisensteinTableBatch, FixedBaseDescription, FixedBaseTable, PreparedAffinePoint, Vesta,
    VestaAffine, VestaProjective,
};
use udon::field::{Fp, Fq};
use udon::msm::Bases;

/// Owner of the expanded table for one circuit commitment generator.
pub(crate) struct FixedGenerator {
    prepared: crate::primitives::prepared::Generator<Vesta>,
}
impl FixedGenerator {
    pub(crate) fn configured(base: &VestaAffine, section: usize) -> Self {
        let config = crate::tuning::COMMITMENT_TABLES;
        let policy = if section < 6 {
            config.fixed[section - 2]
        } else {
            config.sparse.expect("mask tables")
        };
        Self::with_policy(base, policy, embedded(section))
    }
    fn with_policy(
        base: &VestaAffine,
        policy: tables::FixedPolicy,
        embedded: Option<&[VestaAffine]>,
    ) -> Self {
        let entries = embedded.map_or_else(
            || tables::fixed(base, policy),
            |entries| {
                entries
                    .iter()
                    .map(PreparedAffinePoint::from_affine)
                    .collect()
            },
        );
        Self {
            prepared: crate::primitives::prepared::Generator::from_entries(
                *base,
                FixedBaseDescription {
                    window_bits: policy.width,
                },
                entries,
            ),
        }
    }
    pub(crate) fn table(&self) -> FixedBaseTable<'_, Vesta, PreparedAffinePoint<Vesta>> {
        self.prepared.table()
    }
    /// Joint selection/reduction is a source policy; scratch stays bounded.
    pub(crate) fn sum<const N: usize>(bases: [&Self; N], scalars: &[Fp; N]) -> VestaProjective {
        Self::sum_tables(&bases.map(Self::table), scalars)
    }
    pub(crate) fn sum_tables(
        tables: &[FixedBaseTable<'_, Vesta, PreparedAffinePoint<Vesta>>],
        scalars: &[Fp],
    ) -> VestaProjective {
        if crate::tuning::JOINT_FIXED_SUM {
            FixedBaseTable::sum(
                tables,
                scalars,
                &mut [VestaAffine::GENERATOR; 256],
                &mut [Fq::ZERO; 256],
            )
        } else {
            tables
                .iter()
                .zip(scalars)
                .fold(VestaProjective::IDENTITY, |sum, (table, scalar)| {
                    sum.add(&table.mul(scalar))
                })
        }
    }
    #[cfg(feature = "prover")]
    pub(crate) fn mul(&self, scalar: &Fp) -> VestaProjective {
        self.prepared.mul(scalar)
    }
}

#[cfg(embed_commitment_tables)]
crate::static_data::embed_array! {
    /// Optional affine expansions; their section layout is shared with the host.
    static COMMITMENT_TABLES: [VestaAffine; crate::tuning::COMMITMENT_TABLES.embedded_entries()] = artifact_path!(commitment_tables);
}
fn embedded(section: usize) -> Option<&'static [VestaAffine]> {
    #[cfg(embed_commitment_tables)]
    {
        let config = crate::tuning::COMMITMENT_TABLES;
        if config.embeds(section) {
            let start = config.offset(section);
            return Some(&COMMITMENT_TABLES[start..start + config.entries(section)]);
        }
    }
    let _ = section;
    None
}

/// Owns one expansion and shares its residue codebook with other equal-width banks.
pub(crate) struct SrsGenerators {
    table: SrsTable,
    entries: Vec<PreparedAffinePoint<Vesta>>,
    book: Option<Arc<Codebook>>,
}
impl SrsGenerators {
    pub(crate) fn new(bases: &[VestaAffine], section: usize, book: Option<Arc<Codebook>>) -> Self {
        let policy = crate::tuning::COMMITMENT_TABLES.srs[section];
        Self::load(bases, policy.table, embedded(section), book)
    }
    fn load(
        bases: &[VestaAffine],
        table: SrsTable,
        embedded: Option<&[VestaAffine]>,
        book: Option<Arc<Codebook>>,
    ) -> Self {
        let entries = embedded.map_or_else(
            || tables::srs(bases, table, book.as_deref()),
            |entries| {
                entries
                    .iter()
                    .map(PreparedAffinePoint::from_affine)
                    .collect()
            },
        );
        Self {
            table,
            entries,
            book,
        }
    }
    pub(crate) fn bases<'a>(
        &'a self,
        originals: &'a [PreparedAffinePoint<Vesta>],
    ) -> Bases<'a, Vesta> {
        match self.table {
            SrsTable::None => Bases::Prepared(originals),
            SrsTable::Compact => Bases::CompactPrepared(EisensteinTableBatch::bind(&self.entries)),
            _ => Bases::AlphaPrepared(udon::msm::AlphaTable::bind(
                self.book.as_ref().unwrap().view(),
                &self.entries,
            )),
        }
    }
}

/// A separate odd bank is omitted when the coefficient α bank supplies it.
#[cfg(feature = "prover")]
pub(crate) struct FoldingGenerators {
    entries: Vec<PreparedAffinePoint<Vesta>>,
}
#[cfg(feature = "prover")]
impl FoldingGenerators {
    pub(crate) fn new(bases: &[VestaAffine]) -> Self {
        let config = crate::tuning::COMMITMENT_TABLES;
        let entries = if config.entries(17) == 0 {
            Vec::new()
        } else {
            embedded(17).map_or_else(
                || tables::odd(bases, config.folding.unwrap().width),
                |entries| {
                    entries
                        .iter()
                        .map(PreparedAffinePoint::from_affine)
                        .collect()
                },
            )
        };
        Self { entries }
    }
    pub(crate) fn bases<'a>(&'a self, bases: Bases<'a, Vesta>) -> Bases<'a, Vesta> {
        let Some(policy) = crate::tuning::COMMITMENT_TABLES.folding else {
            return bases;
        };
        let table = if !self.entries.is_empty() {
            udon::msm::OddTable::bind(policy.width, &self.entries, bases.len(), bases.len())
                .expect("validated folding table dimensions")
        } else if let Bases::AlphaPrepared(table) = bases {
            table
                .odd_multiples(policy.width)
                .expect("validated folding width fits coefficient table")
        } else {
            unreachable!("folding policy requires a separate odd bank")
        };
        Bases::OddPrepared(table)
    }
}

/// Retained compact tables for the fixed coefficient SRS. Folded IPA banks
/// keep their own identity-aware representation.
#[cfg(feature = "prover")]
pub(crate) struct CompactGenerators {
    entries: Vec<PreparedAffinePoint<Vesta>>,
}

#[cfg(feature = "prover")]
impl CompactGenerators {
    pub(crate) fn new(bases: &[PreparedAffinePoint<Vesta>]) -> Self {
        let required =
            EisensteinTableBatch::<Vesta, PreparedAffinePoint<Vesta>>::requirements(bases.len())
                .expect("fixed coefficient bank size");
        let mut entries =
            vec![PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR); required.table_entries];
        let mut projective = vec![VestaProjective::IDENTITY; required.projective_scratch];
        let mut field = vec![Fq::ZERO; required.field_scratch];
        EisensteinTableBatch::prepare(
            bases,
            &mut entries,
            &mut projective,
            &mut field,
            TaskBudget::SERIAL,
            &udon::exec::SerialExecutor,
        );
        Self { entries }
    }

    pub(crate) fn bases(&self) -> Bases<'_, Vesta> {
        Bases::CompactPrepared(EisensteinTableBatch::bind(&self.entries))
    }
}

/// Circuit commitment terms retain shared polynomial rows and borrow generators.
#[cfg(feature = "prover")]
pub(crate) enum CommitmentTerm<'a> {
    BorrowedDense {
        bases: Bases<'a, Vesta>,
        scalars: &'a [Fp],
    },
    Dense {
        bases: Bases<'a, Vesta>,
        scalars: Column<Fp>,
    },
    Indexed {
        bases: Bases<'a, Vesta>,
        indices: Column<u32>,
        scalars: Column<Fp>,
    },
    Fixed {
        base: &'a FixedGenerator,
        scalar: Fp,
    },
}

#[cfg(feature = "prover")]
pub(crate) fn execute_terms(
    workspace: &mut MsmWorkspace,
    execution: Execution<'_>,
    terms: &[CommitmentTerm<'_>],
) -> Option<Vec<VestaProjective>> {
    execute_with_side_jobs(workspace, execution, terms, Vec::<()>::new(), |(), _| ())
        .map(|(points, _)| points)
}

#[cfg(feature = "prover")]
pub(crate) fn execute_with_side_jobs<S: Send, R: Send>(
    workspace: &mut MsmWorkspace,
    execution: Execution<'_>,
    terms: &[CommitmentTerm<'_>],
    sides: Vec<S>,
    side: impl Fn(S, Execution<'_>) -> R + Sync,
) -> Option<(Vec<VestaProjective>, Vec<R>)> {
    // Bound simultaneous MSM and side-job storage by the execution budget.
    // Sequential banks reuse records and scratch while retaining result order.
    let limit = (crate::sizing::ACTION_WINDOW * sensei_shared::ADVICE_COLUMNS * 2)
        .min(execution.budget.get().saturating_mul(32).max(64));
    if terms.len() <= limit && sides.len() <= limit {
        return execute_with_side_jobs_inner(workspace, execution, terms, sides, side);
    }
    let mut points = Vec::with_capacity(terms.len());
    let mut results = Vec::with_capacity(sides.len());
    let mut sides = sides.into_iter();
    let mut offset = 0;
    while offset < terms.len() || sides.len() != 0 {
        let end = (offset + limit).min(terms.len());
        let jobs = sides.by_ref().take(limit).collect();
        let (batch, side_results) =
            execute_with_side_jobs_inner(workspace, execution, &terms[offset..end], jobs, &side)?;
        points.extend(batch);
        results.extend(side_results);
        offset = end;
    }
    Some((points, results))
}

#[cfg(feature = "prover")]
fn execute_with_side_jobs_inner<S: Send, R: Send>(
    workspace: &mut MsmWorkspace,
    execution: Execution<'_>,
    terms: &[CommitmentTerm<'_>],
    sides: Vec<S>,
    side: impl Fn(S, Execution<'_>) -> R + Sync,
) -> Option<(Vec<VestaProjective>, Vec<R>)> {
    let inputs = terms
        .iter()
        .filter_map(|term| match term {
            CommitmentTerm::Dense { bases, scalars } => Some(Ok(Input::new(*bases, scalars))),
            CommitmentTerm::BorrowedDense { bases, scalars } => {
                Some(Ok(Input::new(*bases, scalars)))
            }
            CommitmentTerm::Indexed {
                bases,
                indices,
                scalars,
            } => Some(Input::indexed(*bases, indices, scalars)),
            CommitmentTerm::Fixed { .. } => None,
        })
        .collect::<Result<Vec<_>, _>>()
        .ok()?;
    let fixed_terms = terms
        .iter()
        .filter_map(|term| match term {
            CommitmentTerm::Fixed { base, scalar } => Some((*base, *scalar)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let fixed_job = |(base, scalar): (&FixedGenerator, Fp)| base.mul(&scalar);
    let side_job = |item| side(item, execution.serial());
    let mut applications = run::Pair::new(
        run::Map::new(fixed_terms.into_iter(), &fixed_job),
        run::Map::new(sides.into_iter(), &side_job),
    );
    let mut output = vec![VestaProjective::IDENTITY; inputs.len()];
    workspace
        .prepare(&inputs, execution.budget)
        .ok()?
        .execute_with(&mut output, &execution, execution.budget, &mut applications)
        .ok()?;
    let mut polynomials = output.into_iter();
    let mut fixed = applications.left.results().into_iter();
    let points = terms
        .iter()
        .map(|term| match term {
            CommitmentTerm::Fixed { .. } => fixed.next().expect("one output per fixed term"),
            _ => polynomials.next().expect("one output per polynomial"),
        })
        .collect();
    Some((points, applications.right.results()))
}

/// Preparation-time sum; the derived circuit owns the resulting point only.
#[cfg(feature = "prover")]
pub(crate) fn sum_prepared(
    bases: &[PreparedAffinePoint<Vesta>],
    scalars: &[Fp],
) -> Option<VestaProjective> {
    let input = Input::new(Bases::Prepared(bases), scalars);
    let mut workspace = MsmWorkspace::new();
    let mut result = [VestaProjective::IDENTITY];
    workspace
        .prepare(&[input], TaskBudget::SERIAL)
        .ok()?
        .execute(&mut result, &udon::exec::SerialExecutor)
        .ok()?;
    Some(result[0])
}

/// Owns normalization output while Udon borrows initialized output and scratch.
#[cfg(feature = "prover")]
pub(crate) fn normalized<C: udon::curve::PastaCurve>(
    points: &[udon::curve::ProjectivePoint<C>],
) -> Vec<udon::curve::Point<C>> {
    let mut output = alloc::vec![udon::curve::Point::IDENTITY; points.len()];
    let mut scratch = alloc::vec![udon::field::PastaField::ZERO; points.len()];
    udon::curve::batch_normalize(points, &mut output, &mut scratch);
    output
}

#[cfg(all(test, feature = "prover", feature = "verifier"))]
mod tests {
    use super::*;
    use crate::native::srs::{PREPARED_POINTS, PreparedSrs};
    use core::sync::atomic::{AtomicUsize, Ordering};
    use udon::curve::VestaPoint;
    use udon::exec::{SerialExecutor, TaskBudget};

    fn evaluate(bases: Bases<'_, Vesta>, scalars: &[Fp]) -> VestaPoint {
        let mut output = [VestaProjective::IDENTITY];
        MsmWorkspace::new()
            .prepare(&[Input::new(bases, scalars)], TaskBudget::SERIAL)
            .unwrap()
            .execute(&mut output, &SerialExecutor)
            .unwrap();
        output[0].to_point()
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "SRS expansion requires --release")]
    fn all_srs_policies_preserve_full_and_ranged_msms() {
        let srs = PreparedSrs::shared();
        let step = <Fp>::from_u64(7).invert().unwrap();
        let scalars: Vec<_> = (0..sensei_shared::N)
            .map(|i| match i % 5 {
                0 => <Fp>::ZERO,
                1 => <Fp>::ONE,
                2 => <Fp>::ONE.neg(),
                _ => step.mul(&<Fp>::from_u64(i as u64 + 1)),
            })
            .collect();
        for bases in [
            &PREPARED_POINTS.coefficient_bases,
            &PREPARED_POINTS.lagrange_bases,
        ] {
            let originals: Vec<_> = bases.iter().map(PreparedAffinePoint::from_affine).collect();
            let ranges = [
                0..bases.len(),
                0..sensei_shared::INSTANCE_VALUE_COUNT,
                3..13,
                bases.len() - 10..bases.len(),
            ];
            let expected: Vec<_> = ranges
                .iter()
                .map(|range| {
                    evaluate(
                        Bases::Affine(&bases[range.clone()]),
                        &scalars[range.clone()],
                    )
                })
                .collect();
            for table in [
                SrsTable::None,
                SrsTable::Compact,
                SrsTable::Alpha5,
                SrsTable::Alpha6,
                SrsTable::Alpha7,
            ] {
                let book = (table.alpha_width() != 0).then(|| srs.codebook(table.alpha_width()));
                // Exercise the actual runtime loader with both generated and
                // affine-artifact entries, independent of the selected policy.
                let affine = tables::srs::<VestaAffine>(bases, table, book.as_deref());
                for embedded in [None, Some(affine.as_slice())] {
                    let bank = SrsGenerators::load(bases, table, embedded, book.clone());
                    if let Some(book) = &book {
                        assert!(Arc::ptr_eq(book, bank.book.as_ref().unwrap()));
                    }
                    for (range, expected) in ranges.iter().zip(&expected) {
                        assert_eq!(
                            evaluate(
                                bank.bases(&originals).range(range.clone()),
                                &scalars[range.clone()],
                            ),
                            *expected,
                            "{table:?}, embedded={}, range={range:?}",
                            embedded.is_some(),
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn auxiliary_generators_preserve_embedded_and_warmed_products() {
        let scalars = [
            <Fp>::ZERO,
            <Fp>::ONE,
            <Fp>::ONE.neg(),
            <Fp>::from_u64(11).invert().unwrap(),
        ];
        for (index, base) in [
            &PREPARED_POINTS.blind_generator,
            &PREPARED_POINTS.ipa_generator,
        ]
        .into_iter()
        .enumerate()
        {
            let policy = crate::tuning::COMMITMENT_TABLES.fixed[index];
            let affine = tables::fixed::<VestaAffine>(base, policy);
            for embedded in [None, Some(affine.as_slice())] {
                let generator = FixedGenerator::with_policy(base, policy, embedded);
                for scalar in &scalars {
                    assert_eq!(
                        generator.mul(scalar).to_point(),
                        evaluate(
                            Bases::Affine(core::slice::from_ref(base)),
                            core::slice::from_ref(scalar),
                        ),
                    );
                }
            }
        }
    }

    struct CountJoins(AtomicUsize);
    impl Executor for CountJoins {
        fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
        where
            L: FnOnce() -> A + Send,
            R: FnOnce() -> B + Send,
            A: Send,
            B: Send,
        {
            self.0.fetch_add(1, Ordering::Relaxed);
            SerialExecutor.join(left, right)
        }
    }

    #[test]
    fn side_jobs_preserve_commitment_parallelism() {
        let executor = CountJoins(AtomicUsize::new(0));
        let budget = TaskBudget::new(4).unwrap();
        let execution = Execution::new(&executor, budget);
        let bases = vec![PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR); 1024];
        let scalars = Column::new(
            (1..=bases.len())
                .map(|value| <Fp>::from_u64(value as u64).invert().unwrap())
                .collect::<Vec<_>>(),
        );
        let terms = [CommitmentTerm::Dense {
            bases: Bases::Prepared(&bases),
            scalars,
        }];
        let expected = execute_terms(&mut MsmWorkspace::new(), execution, &terms).unwrap();
        let msm_joins = executor.0.swap(0, Ordering::Relaxed);
        assert!(msm_joins > 0, "the commitment exposes parallel work");
        for side_count in [0, 3] {
            let (commitments, sides) = execute_with_side_jobs(
                &mut MsmWorkspace::new(),
                execution,
                &terms,
                (0..side_count).collect(),
                |index, execution| (index, execution.budget),
            )
            .unwrap();
            assert_eq!(commitments, expected);
            assert_eq!(
                sides,
                (0..side_count)
                    .map(|index| (index, TaskBudget::SERIAL))
                    .collect::<Vec<_>>()
            );
            assert!(executor.0.swap(0, Ordering::Relaxed) >= msm_joins);
        }
    }
}
