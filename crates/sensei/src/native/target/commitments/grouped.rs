//! Equal coefficients share a sum of their commitment bases.

use alloc::vec::Vec;
use std::collections::{HashMap, hash_map::Entry};

use super::{Column, Fp, PreparedAffinePoint, Vesta, VestaProjective, normalized};

pub(super) struct GroupedRow {
    pub(super) bases: Vec<PreparedAffinePoint<Vesta>>,
    pub(super) scalars: Column<Fp>,
}

/// Rewrites `sum_i [a_i] G_i` as `sum_v [v] (sum_{i: a_i = v} G_i)`.
///
/// Zero coefficients disappear. Groups follow first occurrence, independently
/// of hash iteration order, and equality uses reduced field representatives.
/// Singleton groups keep their original prepared bases. A combined base that
/// cancels uses a zero coefficient on its original nonidentity representative.
///
/// The advice caller supplies exactly `N` terms. Output storage has at most
/// one entry per input; temporary group sums and normalization scratch have
/// at most one entry per repeated group. Nothing is retained between batches.
pub(super) fn group_equal_scalars(
    bases: &[PreparedAffinePoint<Vesta>],
    scalars: &[Fp],
) -> GroupedRow {
    assert_eq!(bases.len(), scalars.len());
    group_terms(
        bases.iter().copied().zip(scalars.iter().copied()),
        scalars.iter().filter(|scalar| !scalar.is_zero()).count(),
    )
}

fn group_terms(
    terms: impl Iterator<Item = (PreparedAffinePoint<Vesta>, Fp)>,
    capacity: usize,
) -> GroupedRow {
    let mut index = HashMap::with_capacity(capacity);
    let mut representatives = Vec::with_capacity(capacity);
    let mut values = Vec::with_capacity(capacity);
    let mut group_points = Vec::<Option<usize>>::with_capacity(capacity);
    let mut points = Vec::<VestaProjective>::new();
    let mut point_groups = Vec::new();
    for (base, scalar) in terms {
        if scalar.is_zero() {
            continue;
        }
        match index.entry(scalar.reduce().montgomery_limbs()) {
            Entry::Vacant(entry) => {
                entry.insert(values.len());
                representatives.push(base);
                values.push(scalar);
                group_points.push(None);
            }
            Entry::Occupied(entry) => {
                let group = *entry.get();
                if let Some(point) = group_points[group] {
                    points[point] = points[point].add_mixed(&base.to_affine());
                } else {
                    group_points[group] = Some(points.len());
                    point_groups.push(group);
                    points.push(
                        representatives[group]
                            .to_affine()
                            .to_projective()
                            .add_mixed(&base.to_affine()),
                    );
                }
            }
        }
    }
    for (point, group) in normalized(&points).iter().zip(point_groups) {
        if let Some(affine) = point.as_affine() {
            representatives[group] = PreparedAffinePoint::from_affine(affine);
        } else {
            values[group] = Fp::ZERO;
        }
    }
    GroupedRow {
        bases: representatives,
        scalars: Column::new(values),
    }
}

/// Same-column members of copy classes that remain after structured carve-outs.
/// Runtime equality is checked because commitment helpers also accept arbitrary
/// columns; a failed equality check restores the original terms.
pub(crate) struct ResidualCopies {
    columns: [CopyColumn; sensei_shared::ADVICE_COLUMNS],
}
struct CopyColumn {
    membership: Vec<u16>,
    groups: Vec<CopyGroup>,
}
struct CopyGroup {
    rows: Vec<u16>,
    base: Option<PreparedAffinePoint<Vesta>>,
}
impl ResidualCopies {
    pub(super) fn new(
        bases: &[PreparedAffinePoint<Vesta>],
        classes: &super::super::copy_constraints::CopyClasses,
        excluded: &[(usize, usize)],
    ) -> Result<Self, super::TargetError> {
        use crate::native::queries::{ColumnKind, PERMUTATION_COLUMNS};
        use sensei_shared::{ADVICE_COLUMNS, N, USABLE_ROWS_END};
        let mut columns: [CopyColumn; ADVICE_COLUMNS] = core::array::from_fn(|_| CopyColumn {
            membership: alloc::vec![u16::MAX; N],
            groups: Vec::new(),
        });
        for class in classes.classes() {
            let mut rows: [Vec<u16>; ADVICE_COLUMNS] = core::array::from_fn(|_| Vec::new());
            for &cell in class {
                let row = usize::from(cell) % N;
                let column = PERMUTATION_COLUMNS
                    .get(usize::from(cell) / N)
                    .ok_or(super::TargetError::Malformed)?;
                if column.kind == ColumnKind::Advice
                    && row < USABLE_ROWS_END
                    && excluded.binary_search(&(column.index, row)).is_err()
                {
                    rows[column.index].push(row as u16);
                }
            }
            for (column, mut rows) in columns.iter_mut().zip(rows) {
                if rows.len() < 2 {
                    continue;
                }
                rows.sort_unstable();
                let group = u16::try_from(column.groups.len())
                    .map_err(|_| super::TargetError::Malformed)?;
                for &row in &rows {
                    if column.membership[usize::from(row)] != u16::MAX {
                        return Err(super::TargetError::Malformed);
                    }
                    column.membership[usize::from(row)] = group;
                }
                column.groups.push(CopyGroup { rows, base: None });
            }
        }
        let sums = columns
            .iter()
            .flat_map(|column| &column.groups)
            .map(|group| {
                group
                    .rows
                    .iter()
                    .fold(VestaProjective::IDENTITY, |sum, &row| {
                        sum.add_mixed(&bases[usize::from(row)].to_affine())
                    })
            })
            .collect::<Vec<_>>();
        for (group, point) in columns
            .iter_mut()
            .flat_map(|column| &mut column.groups)
            .zip(normalized(&sums))
        {
            group.base = point.as_affine().map(PreparedAffinePoint::from_affine);
        }
        Ok(Self { columns })
    }

    pub(super) fn group(
        &self,
        bases: &[PreparedAffinePoint<Vesta>],
        scalars: &[Fp],
        column: usize,
    ) -> GroupedRow {
        let Some(column) = self.columns.get(column) else {
            return group_equal_scalars(bases, scalars);
        };
        let equal = column
            .groups
            .iter()
            .map(|group| {
                let first = scalars[usize::from(group.rows[0])].reduce();
                group.rows[1..]
                    .iter()
                    .all(|&row| scalars[usize::from(row)].reduce() == first)
            })
            .collect::<Vec<_>>();
        let terms = bases
            .iter()
            .zip(scalars)
            .enumerate()
            .filter_map(|(row, (&base, &scalar))| {
                let id = column.membership[row];
                if id == u16::MAX || !equal[usize::from(id)] {
                    return Some((base, scalar));
                }
                let group = &column.groups[usize::from(id)];
                if row == usize::from(group.rows[0]) {
                    group.base.map(|base| (base, scalar))
                } else {
                    None
                }
            });
        group_terms(
            terms,
            scalars.iter().filter(|scalar| !scalar.is_zero()).count(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::commitment::{CommitmentTerm, MsmWorkspace, execute_terms};
    use crate::native::curve::VestaAffine;
    use udon::field::{PallasBase, PrimeModulus};

    #[test]
    fn residual_copy_classes_match_dense_with_fallbacks() {
        use crate::native::target::copy_constraints::CopyClasses;
        use sensei_shared::{N, USABLE_ROWS_END};
        // Include a carved-out row, a tail row, and a second advice column.
        let classes = CopyClasses {
            members: vec![
                N as u16,
                (N + 1) as u16,
                (N + 2) as u16,
                (2 * N) as u16,
                (N + 3) as u16,
                (N + 4) as u16,
                (N + 5) as u16,
                (N + USABLE_ROWS_END) as u16,
            ],
            starts: vec![0, 4, 6, 8],
        };
        let mut bases = vec![PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR); N];
        bases[4] = PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR.neg());
        let copies = ResidualCopies::new(&bases, &classes, &[(0, 2)]).unwrap();
        assert_eq!(copies.columns[0].groups.len(), 2);
        assert!(copies.columns[0].groups[1].base.is_none());
        assert!(copies.columns[1].groups.is_empty());
        let loose_zero = Fp::from_montgomery_limbs(PallasBase::MODULUS);
        for value in [
            Fp::ZERO,
            loose_zero,
            Fp::ONE,
            <Fp>::ONE.neg(),
            Fp::from_bytes_reduced(&[0x5a; 32]),
        ] {
            for unequal in [false, true] {
                let mut scalars = vec![Fp::ZERO; N];
                scalars[0] = value;
                scalars[1] = if unequal {
                    value.add(&<Fp>::ONE)
                } else {
                    value.add(&loose_zero)
                };
                scalars[2] = Fp::from_u64(17);
                scalars[3] = value;
                scalars[4] = value;
                scalars[5] = Fp::from_u64(19);
                scalars[USABLE_ROWS_END] = Fp::from_u64(23);
                let expected = bases
                    .iter()
                    .zip(&scalars)
                    .fold(VestaProjective::IDENTITY, |sum, (base, scalar)| {
                        sum.add(&base.to_affine().mul_projective(scalar))
                    });
                let grouped = copies.group(&bases, &scalars, 0);
                let actual = grouped
                    .bases
                    .iter()
                    .zip(grouped.scalars.iter())
                    .fold(VestaProjective::IDENTITY, |sum, (base, scalar)| {
                        sum.add(&base.to_affine().mul_projective(scalar))
                    });
                assert_eq!(actual, expected);
            }
        }
    }

    #[test]
    fn residual_copy_census_excludes_carveouts_and_tails() {
        let copies = &crate::test_codec::target().parameters().residual_copies;
        let groups = copies
            .columns
            .iter()
            .flat_map(|column| &column.groups)
            .collect::<Vec<_>>();
        assert_eq!(groups.len(), 111);
        assert_eq!(
            groups.iter().map(|group| group.rows.len()).sum::<usize>(),
            237
        );
        assert!(groups.iter().all(|group| {
            group
                .rows
                .iter()
                .all(|&row| usize::from(row) < sensei_shared::USABLE_ROWS_END)
        }));
    }

    fn bases(multiples: &[u64]) -> Vec<PreparedAffinePoint<Vesta>> {
        let points = multiples
            .iter()
            .map(|multiple| VestaAffine::GENERATOR.mul_projective(&Fp::from_u64(*multiple)))
            .collect::<Vec<_>>();
        normalized(&points)
            .iter()
            .map(|point| PreparedAffinePoint::from_affine(point.as_affine().unwrap()))
            .collect()
    }

    fn checked_group(bases: &[PreparedAffinePoint<Vesta>], scalars: &[Fp]) -> GroupedRow {
        // Individual scalar multiplication is independent of grouping and MSM.
        let expected = bases
            .iter()
            .zip(scalars)
            .fold(VestaProjective::IDENTITY, |sum, (base, scalar)| {
                sum.add(&base.to_affine().mul_projective(scalar))
            });
        let grouped = group_equal_scalars(bases, scalars);
        let terms = [CommitmentTerm::Dense {
            bases: udon::msm::Bases::Prepared(&grouped.bases),
            scalars: grouped.scalars.clone(),
        }];
        let actual = execute_terms(
            &mut MsmWorkspace::new(),
            crate::test_codec::execution(),
            &terms,
        )
        .unwrap();
        assert_eq!(actual, [expected]);
        grouped
    }

    #[test]
    fn empty_and_zero_rows_commit_to_identity() {
        let empty = checked_group(&[], &[]);
        assert!(empty.bases.is_empty());
        assert!(empty.scalars.is_empty());

        let loose_zero = Fp::from_montgomery_limbs(PallasBase::MODULUS);
        let zeros = checked_group(&bases(&[1, 2, 3]), &[Fp::ZERO, loose_zero, Fp::ZERO]);
        assert!(zeros.bases.is_empty());
        assert!(zeros.scalars.is_empty());
    }

    #[test]
    fn interleaved_groups_compare_field_values_and_keep_singletons() {
        let loose_zero = Fp::from_montgomery_limbs(PallasBase::MODULUS);
        let loose_one = <Fp>::ONE.add(&loose_zero);
        assert_ne!(loose_one.montgomery_limbs(), <Fp>::ONE.montgomery_limbs());
        let full_width = <Fp>::ONE.neg();
        let singleton = Fp::from_bytes_reduced(&[0x5a; 32]);
        let bases = bases(&[1, 2, 3, 4, 5, 6, 7]);
        let scalars = [
            loose_one,
            full_width,
            singleton,
            Fp::ONE,
            full_width,
            Fp::ONE,
            loose_zero,
        ];
        let grouped = checked_group(&bases, &scalars);
        assert_eq!(grouped.bases.len(), 3);
        assert_eq!(
            grouped
                .scalars
                .iter()
                .map(|scalar| scalar.reduce())
                .collect::<Vec<_>>(),
            [<Fp>::ONE.reduce(), full_width.reduce(), singleton.reduce()]
        );
        assert_eq!(
            grouped.bases[2].to_affine().to_projective(),
            bases[2].to_affine().to_projective()
        );
    }

    #[test]
    fn group_sums_can_cancel_and_resume_from_identity() {
        let generator = VestaAffine::GENERATOR;
        let positive = PreparedAffinePoint::from_affine(&generator);
        let negative = PreparedAffinePoint::from_affine(&generator.neg());
        let doubled = bases(&[2])[0];
        let three = Fp::from_u64(3);
        let seven = Fp::from_u64(7);
        let grouped = checked_group(
            &[positive, negative, positive, negative, doubled],
            &[three, three, seven, seven, seven],
        );
        assert_eq!(grouped.bases.len(), 2);
        assert!(grouped.scalars[0].is_zero());
        assert_eq!(grouped.scalars[1].reduce(), seven.reduce());
        assert_eq!(
            grouped.bases[1].to_affine().to_projective(),
            doubled.to_affine().to_projective()
        );
    }
}
