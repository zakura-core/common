//! Physical and virtual generator folds agree, including cancellation.

use super::*;
use crate::resource_tests::PoolExecutor;
use alloc::vec;
use udon::msm::OddTable;

fn points(generators: &Generators) -> Vec<VestaPoint> {
    match generators {
        Generators::Prepared(points) => points.iter().map(|p| p.to_affine().to_point()).collect(),
        Generators::Points(points) => points.to_vec(),
        Generators::Compact(points) => {
            let Bases::CompactPrepared(table) = points.bases() else {
                unreachable!()
            };
            table
                .as_slice()
                .chunks_exact(8)
                .map(|row| row[0].to_affine().to_point())
                .collect()
        }
    }
}

fn recursive_fold(mut points: Vec<VestaPoint>, challenges: &[Fp]) -> Vec<VestaPoint> {
    for challenge in challenges {
        let half = points.len() / 2;
        for i in 0..half {
            points[i] = points[i]
                .to_projective()
                .add(&points[i + half].mul_projective(challenge))
                .to_point();
        }
        points.truncate(half);
    }
    points
}

fn weights(challenges: &[Fp]) -> Vec<Fp> {
    let mut weights = vec![Fp::ONE];
    for challenge in challenges {
        weights = weights
            .iter()
            .flat_map(|weight| [*weight, weight.mul(challenge)])
            .collect();
    }
    weights
}

#[test]
fn shared_weights_match_recursive_folds_on_selected_pools() {
    let bases = crate::test_codec::target()
        .parameters()
        .coefficient_generators();
    let initial = bases
        .iter()
        .map(|p| p.to_affine().to_point())
        .collect::<Vec<_>>();
    let odd_entries = sensei_shared::commitment_tables::odd::<PreparedAffinePoint<Vesta>>(
        &bases.iter().map(|p| p.to_affine()).collect::<Vec<_>>(),
        5,
    );
    let odd = OddTable::bind(5, &odd_entries, bases.len(), bases.len()).unwrap();
    let challenges = [
        <Fp>::from_u64(0xd6e8_feb8_6659_fd93).square().square(),
        <Fp>::ONE,
        <Fp>::from_u64(0x9e37_79b9_7f4a_7c15).square().neg(),
        <Fp>::ONE.neg(),
        <Fp>::from_u64(29).invert().unwrap(),
        <Fp>::from_u64(0xa5a5_5a5a_1234_5678).square().square(),
    ];
    let first = recursive_fold(initial, &challenges[..3]);
    let second = recursive_fold(first.clone(), &challenges[3..]);
    for workers in [1, 3, 16] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap();
        let executor = PoolExecutor(&pool);
        let execution = Execution::new(&executor, TaskBudget::new(workers).unwrap());
        // Enter the selected pool to exercise nested dispatch, including the
        // case where only one worker can make progress.
        let mut workspace = Workspace::default();
        for bank in [
            Bases::Prepared(bases),
            crate::test_codec::target().parameters().coefficient_bases(),
            crate::test_codec::target().parameters().folding_bases(),
            Bases::OddPrepared(odd),
        ] {
            for iteration in 0..3 {
                workspace.dirty();
                let before = workspace.capacities();
                pool.install(|| {
                    let folded =
                        materialize(&mut workspace, bank, &weights(&challenges[..3]), execution)
                            .unwrap();
                    assert_eq!(points(&folded), first);
                    let next = materialize(
                        &mut workspace,
                        folded.bases(),
                        &weights(&challenges[3..]),
                        execution,
                    )
                    .unwrap();
                    assert_eq!(points(&next), second);
                    // The old lease remains valid until its replacement is complete.
                    assert_eq!(points(&folded), first);
                });
                if iteration != 0 {
                    assert_eq!(workspace.capacities(), before);
                }
            }
        }
    }
}

#[test]
fn cancellation_and_zero_weights_survive_further_folds() {
    let low = (1..=32)
        .map(|i| {
            VestaPoint::GENERATOR
                .mul_projective(&Fp::from_u64(i))
                .to_point()
        })
        .collect::<Vec<_>>();
    let mut initial = low.clone();
    initial.extend(low.iter().enumerate().map(|(i, point)| {
        if i % 2 == 0 {
            *point
        } else {
            point.add(&VestaPoint::GENERATOR).to_point()
        }
    }));
    let prepared = initial
        .iter()
        .map(|p| PreparedAffinePoint::from_affine(p.as_affine().unwrap()))
        .collect::<Vec<_>>();
    let compact = crate::native::commitment::CompactGenerators::new(&prepared);
    let odd_entries = sensei_shared::commitment_tables::odd::<PreparedAffinePoint<Vesta>>(
        &initial
            .iter()
            .map(|p| *p.as_affine().unwrap())
            .collect::<Vec<_>>(),
        6,
    );
    let odd = OddTable::bind(6, &odd_entries, prepared.len(), prepared.len()).unwrap();
    let mut workspace = Workspace::default();
    // These small weights let the shared planner use the original odd-table
    // bases; cancellation must still select identity-capable folded storage.
    for bank in [
        Bases::Prepared(&prepared),
        compact.bases(),
        Bases::OddPrepared(odd),
    ] {
        let mut folded: Option<Generators> = None;
        let mut expected = initial.clone();
        for challenge in [
            <Fp>::ONE.neg(),
            <Fp>::ZERO,
            <Fp>::from_u64(13),
            <Fp>::ONE.neg(),
        ] {
            expected = recursive_fold(expected, &[challenge]);
            workspace.dirty();
            let next = materialize(
                &mut workspace,
                folded.as_ref().map_or(bank, Generators::bases),
                &weights(&[challenge]),
                crate::test_codec::execution(),
            )
            .unwrap();
            assert_eq!(points(&next), expected);
            assert!(matches!(next, Generators::Points(_)));
            folded = Some(next);
        }
        assert!(
            points(folded.as_ref().unwrap())
                .iter()
                .all(VestaPoint::is_identity)
        );
    }
}
