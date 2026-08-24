//! This module contains an optimisation of the polynomial commitment opening
//! scheme described in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021

use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;

use super::*;
use crate::{arithmetic::CurveAffine, transcript::ChallengeScalar};

mod prover;
mod verifier;

pub use prover::create_proof;
pub use verifier::verify_proof;

#[derive(Clone, Copy, Debug)]
struct X1 {}
/// Challenge for compressing openings at the same point sets together.
type ChallengeX1<F> = ChallengeScalar<F, X1>;

#[derive(Clone, Copy, Debug)]
struct X2 {}
/// Challenge for keeping the multi-point quotient polynomial terms linearly independent.
type ChallengeX2<F> = ChallengeScalar<F, X2>;

#[derive(Clone, Copy, Debug)]
struct X3 {}
/// Challenge point at which the commitments are opened.
type ChallengeX3<F> = ChallengeScalar<F, X3>;

#[derive(Clone, Copy, Debug)]
struct X4 {}
/// Challenge for collapsing the openings of the various remaining polynomials at x_3
/// together.
type ChallengeX4<F> = ChallengeScalar<F, X4>;

/// A polynomial query at a point
#[derive(Debug, Clone)]
pub struct ProverQuery<'a, C: CurveAffine> {
    /// point at which polynomial is queried
    pub point: C::Scalar,
    /// coefficients of polynomial
    pub poly: &'a Polynomial<C::Scalar, Coeff>,
    /// blinding factor of polynomial
    pub blind: commitment::Blind<C::Scalar>,
}

/// A polynomial query at a point
#[derive(Debug, Clone)]
pub struct VerifierQuery<'r, 'params: 'r, C: CurveAffine> {
    /// point at which polynomial is queried
    point: C::Scalar,
    /// commitment to polynomial
    commitment: CommitmentReference<'r, 'params, C>,
    /// evaluation of polynomial at query point
    eval: C::Scalar,
}

impl<'r, 'params: 'r, C: CurveAffine> VerifierQuery<'r, 'params, C> {
    /// Create a new verifier query based on a commitment
    pub fn new_commitment(commitment: &'r C, point: C::Scalar, eval: C::Scalar) -> Self {
        VerifierQuery {
            point,
            eval,
            commitment: CommitmentReference::Commitment(commitment),
        }
    }

    /// Create a new verifier query based on a linear combination of commitments
    pub fn new_msm(
        msm: &'r commitment::MSM<'params, C>,
        point: C::Scalar,
        eval: C::Scalar,
    ) -> Self {
        VerifierQuery {
            point,
            eval,
            commitment: CommitmentReference::MSM(msm),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
#[derive(Copy, Clone, Debug)]
enum CommitmentReference<'r, 'params: 'r, C: CurveAffine> {
    Commitment(&'r C),
    MSM(&'r commitment::MSM<'params, C>),
}

impl<'r, 'params: 'r, C: CurveAffine> PartialEq for CommitmentReference<'r, 'params, C> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (&CommitmentReference::Commitment(a), &CommitmentReference::Commitment(b)) => {
                std::ptr::eq(a, b)
            }
            (&CommitmentReference::MSM(a), &CommitmentReference::MSM(b)) => std::ptr::eq(a, b),
            _ => false,
        }
    }
}

impl<'r, 'params: 'r, C: CurveAffine> Eq for CommitmentReference<'r, 'params, C> {}

impl<'r, 'params: 'r, C: CurveAffine> Hash for CommitmentReference<'r, 'params, C> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match *self {
            CommitmentReference::Commitment(a) => std::ptr::hash(a, state),
            CommitmentReference::MSM(a) => std::ptr::hash(a, state),
        }
    }
}

#[derive(Debug)]
struct CommitmentData<F, T: PartialEq> {
    commitment: T,
    set_index: usize,
    point_indices: Vec<usize>,
    evals: Vec<F>,
}

impl<F, T: PartialEq> CommitmentData<F, T> {
    fn new(commitment: T) -> Self {
        CommitmentData {
            commitment,
            set_index: 0,
            point_indices: vec![],
            evals: vec![],
        }
    }
}

trait Query<F>: Sized {
    type Commitment: Eq + Hash + Copy;
    type Eval: Clone + Default;

    fn get_point(&self) -> F;
    fn get_eval(&self) -> Self::Eval;
    fn get_commitment(&self) -> Self::Commitment;
}

type IntermediateSets<F, Q> = (
    Vec<CommitmentData<<Q as Query<F>>::Eval, <Q as Query<F>>::Commitment>>,
    Vec<Vec<F>>,
);

/// Returns `None` if `queries` is empty or contains the same point and
/// commitment more than once.
fn construct_intermediate_sets<F: Field + Ord, I, Q: Query<F>>(
    queries: I,
) -> Option<IntermediateSets<F, Q>>
where
    I: IntoIterator<Item = Q> + Clone,
{
    // Construct sets of unique commitments and corresponding information about
    // their queries. The vector is in first-seen order; the prover and verifier
    // both iterate the returned commitment data in this order, so it feeds the
    // transcript and must be deterministic. The side index keeps lookups O(1):
    // when many proof instances are batched into one call, both the query
    // count and the number of distinct (pointer-identity) commitments grow
    // with the instance count, and a linear scan would make this quadratic.
    let mut commitment_map: Vec<(Q::Commitment, CommitmentData<Q::Eval, ()>)> = Vec::new();
    let mut commitment_indices: HashMap<Q::Commitment, usize> = HashMap::new();

    // Also construct mapping from a unique point to a point_index. This defines
    // an ordering on the points.
    let mut point_index_map = BTreeMap::new();
    let mut points = Vec::new();

    // Iterate once over all queries, computing the ordering of the points and
    // collecting each commitment's evaluations.
    for query in queries {
        let point = query.get_point();
        let point_idx = *point_index_map.entry(point).or_insert_with(|| {
            let point_idx = points.len();
            points.push(point);
            point_idx
        });

        let commitment = query.get_commitment();
        let commitment_idx = *commitment_indices.entry(commitment).or_insert_with(|| {
            commitment_map.push((commitment, CommitmentData::new(())));
            commitment_map.len() - 1
        });
        let commitment_data = &mut commitment_map[commitment_idx].1;
        if commitment_data.point_indices.contains(&point_idx) {
            // Caller tried to provide two evaluations for the same commitment
            // at the same point. Permitting this would be unsound.
            return None;
        }
        commitment_data.point_indices.push(point_idx);
        commitment_data.evals.push(query.get_eval());
    }

    if commitment_map.is_empty() {
        return None;
    }

    // Construct map of unique ordered point_idx_sets to their set_idx
    let mut point_idx_sets = BTreeMap::new();

    let commitment_map = commitment_map
        .into_iter()
        .map(|(commitment, commitment_data)| {
            let mut indexed_evals = commitment_data
                .point_indices
                .iter()
                .copied()
                .zip(commitment_data.evals)
                .collect::<Vec<_>>();
            indexed_evals.sort_unstable_by_key(|(point_idx, _)| *point_idx);

            let point_idx_set = indexed_evals
                .iter()
                .map(|(point_idx, _)| *point_idx)
                .collect::<Vec<_>>();
            let num_sets = point_idx_sets.len();
            let set_index = *point_idx_sets.entry(point_idx_set).or_insert(num_sets);

            CommitmentData {
                commitment,
                set_index,
                point_indices: commitment_data.point_indices,
                evals: indexed_evals.into_iter().map(|(_, eval)| eval).collect(),
            }
        })
        .collect();

    // Get actual points in each point set
    let mut point_sets: Vec<Vec<F>> = vec![Vec::new(); point_idx_sets.len()];
    for (point_idx_set, set_idx) in point_idx_sets {
        point_sets[set_idx] = point_idx_set
            .into_iter()
            .map(|point_idx| points[point_idx])
            .collect();
    }

    Some((commitment_map, point_sets))
}

#[test]
fn test_empty_queries() {
    use assert_matches::assert_matches;
    use rand::rng;

    use super::commitment::Params;
    use crate::pasta::EqAffine;
    use crate::transcript::Challenge255;

    let params = Params::<EqAffine>::new(1);
    let mut transcript = crate::transcript::Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let error = create_proof(
        &params,
        rng(),
        &mut transcript,
        std::iter::empty::<ProverQuery<'_, EqAffine>>(),
    )
    .expect_err("empty query sets must be rejected");
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);

    let mut proof = &[][..];
    let mut transcript = crate::transcript::Blake2bRead::<_, _, Challenge255<_>>::init(&mut proof);
    assert_matches!(
        verify_proof(
            &params,
            &mut transcript,
            std::iter::empty::<VerifierQuery<'_, '_, EqAffine>>(),
            params.empty_msm(),
        ),
        Err(Error::OpeningError)
    );
}

#[test]
fn test_roundtrip() {
    use group::Curve;
    use rand::rng;

    use super::commitment::{Blind, Params};
    use crate::arithmetic::eval_polynomial;
    use crate::pasta::{EqAffine, Fp};
    use crate::transcript::Challenge255;

    const K: u32 = 4;

    let params: Params<EqAffine> = Params::new(K);
    let domain = EvaluationDomain::new(1, K);
    let mut rng = rng();

    let mut ax = domain.empty_coeff();
    for (i, a) in ax.iter_mut().enumerate() {
        *a = Fp::from(10 + i as u64);
    }

    let mut bx = domain.empty_coeff();
    for (i, a) in bx.iter_mut().enumerate() {
        *a = Fp::from(100 + i as u64);
    }

    let mut cx = domain.empty_coeff();
    for (i, a) in cx.iter_mut().enumerate() {
        *a = Fp::from(100 + i as u64);
    }

    let blind = Blind(Fp::random(&mut rng));

    let a = params.commit(&ax, blind).to_affine();
    let b = params.commit(&bx, blind).to_affine();
    let c = params.commit(&cx, blind).to_affine();

    let x = Fp::random(&mut rng);
    let y = Fp::random(&mut rng);
    let avx = eval_polynomial(&ax, x);
    let bvx = eval_polynomial(&bx, x);
    let cvy = eval_polynomial(&cx, y);

    let mut transcript = crate::transcript::Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(
        &params,
        rng,
        &mut transcript,
        std::iter::empty()
            .chain(Some(ProverQuery {
                point: x,
                poly: &ax,
                blind,
            }))
            .chain(Some(ProverQuery {
                point: x,
                poly: &bx,
                blind,
            }))
            .chain(Some(ProverQuery {
                point: y,
                poly: &cx,
                blind,
            })),
    )
    .unwrap();
    let proof = transcript.finalize();

    {
        let mut proof = &proof[..];
        let mut transcript =
            crate::transcript::Blake2bRead::<_, _, Challenge255<_>>::init(&mut proof);
        let msm = params.empty_msm();

        let guard = verify_proof(
            &params,
            &mut transcript,
            std::iter::empty()
                .chain(Some(VerifierQuery::new_commitment(&a, x, avx)))
                .chain(Some(VerifierQuery::new_commitment(&b, x, avx))) // NB: wrong!
                .chain(Some(VerifierQuery::new_commitment(&c, y, cvy))),
            msm,
        )
        .unwrap();

        // Should fail.
        assert!(!guard.use_challenges().eval());
    }

    {
        let mut proof = &proof[..];

        let mut transcript =
            crate::transcript::Blake2bRead::<_, _, Challenge255<_>>::init(&mut proof);
        let msm = params.empty_msm();

        let guard = verify_proof(
            &params,
            &mut transcript,
            std::iter::empty()
                .chain(Some(VerifierQuery::new_commitment(&a, x, avx)))
                .chain(Some(VerifierQuery::new_commitment(&b, x, bvx)))
                .chain(Some(VerifierQuery::new_commitment(&c, y, cvy))),
            msm,
        )
        .unwrap();

        // Should succeed.
        assert!(guard.use_challenges().eval());
    }
}

#[test]
fn test_identical_queries() {
    use assert_matches::assert_matches;
    use group::Curve;
    use rand::rng;

    use super::commitment::{Blind, Params};
    use crate::arithmetic::eval_polynomial;
    use crate::pasta::{EqAffine, Fp};
    use crate::transcript::Challenge255;

    const K: u32 = 4;

    let params: Params<EqAffine> = Params::new(K);
    let domain = EvaluationDomain::new(1, K);
    let mut rng = rng();

    let mut ax = domain.empty_coeff();
    for (i, a) in ax.iter_mut().enumerate() {
        *a = Fp::from(10 + i as u64);
    }

    let mut bx = domain.empty_coeff();
    for (i, a) in bx.iter_mut().enumerate() {
        *a = Fp::from(100 + i as u64);
    }

    let mut cx = domain.empty_coeff();
    for (i, a) in cx.iter_mut().enumerate() {
        *a = Fp::from(100 + i as u64);
    }

    let blind = Blind(Fp::random(&mut rng));

    let a = params.commit(&ax, blind).to_affine();
    let b = params.commit(&bx, blind).to_affine();
    let c = params.commit(&cx, blind).to_affine();

    let x = Fp::random(&mut rng);
    let y = Fp::random(&mut rng);
    let avx = eval_polynomial(&ax, x);
    let bvx = eval_polynomial(&bx, x);
    let bvx_bad = Fp::random(&mut rng);
    let cvy = eval_polynomial(&cx, y);

    let mut transcript = crate::transcript::Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(
        &params,
        rng,
        &mut transcript,
        std::iter::empty()
            .chain(Some(ProverQuery {
                point: x,
                poly: &ax,
                blind,
            }))
            .chain(Some(ProverQuery {
                point: x,
                poly: &bx,
                blind,
            }))
            .chain(Some(ProverQuery {
                point: y,
                poly: &cx,
                blind,
            })),
    )
    .unwrap();
    let proof = transcript.finalize();

    {
        let mut proof = &proof[..];

        let mut transcript =
            crate::transcript::Blake2bRead::<_, _, Challenge255<_>>::init(&mut proof);
        let msm = params.empty_msm();

        assert_matches!(
            verify_proof(
                &params,
                &mut transcript,
                std::iter::empty()
                    .chain(Some(VerifierQuery::new_commitment(&a, x, avx)))
                    .chain(Some(VerifierQuery::new_commitment(&b, x, bvx_bad))) // This is wrong.
                    .chain(Some(VerifierQuery::new_commitment(&b, x, bvx)))
                    .chain(Some(VerifierQuery::new_commitment(&c, y, cvy))),
                msm,
            ),
            Err(Error::OpeningError)
        );
    }
}

#[cfg(test)]
mod proptests {
    use group::ff::FromUniformBytes;
    use proptest::{
        collection::{hash_set, vec},
        prelude::*,
        sample::select,
    };

    use super::construct_intermediate_sets;
    use pasta_curves::Fp;

    use std::{cell::Cell, convert::TryFrom};

    #[derive(Debug, Clone)]
    struct MyQuery<F> {
        point: F,
        eval: F,
        commitment: usize,
    }

    impl super::Query<Fp> for MyQuery<Fp> {
        type Commitment = usize;
        type Eval = Fp;

        fn get_point(&self) -> Fp {
            self.point
        }

        fn get_eval(&self) -> Self::Eval {
            self.eval
        }

        fn get_commitment(&self) -> Self::Commitment {
            self.commitment
        }
    }

    #[test]
    fn intermediate_sets_preserve_query_order_in_one_traversal() {
        let queries = vec![
            MyQuery {
                point: Fp::from(2),
                eval: Fp::from(72),
                commitment: 7,
            },
            MyQuery {
                point: Fp::from(0),
                eval: Fp::from(30),
                commitment: 3,
            },
            MyQuery {
                point: Fp::from(1),
                eval: Fp::from(111),
                commitment: 11,
            },
            MyQuery {
                point: Fp::from(1),
                eval: Fp::from(71),
                commitment: 7,
            },
            MyQuery {
                point: Fp::from(0),
                eval: Fp::from(90),
                commitment: 9,
            },
            MyQuery {
                point: Fp::from(1),
                eval: Fp::from(31),
                commitment: 3,
            },
            MyQuery {
                point: Fp::from(2),
                eval: Fp::from(112),
                commitment: 11,
            },
        ];
        let query_count = queries.len();
        let traversed = Cell::new(0);
        let queries = queries.into_iter().map(|query| {
            traversed.set(traversed.get() + 1);
            query
        });

        let (commitment_data, point_sets) =
            construct_intermediate_sets(queries).expect("queries are distinct");

        assert_eq!(traversed.get(), query_count);
        assert_eq!(
            commitment_data
                .iter()
                .map(|data| data.commitment)
                .collect::<Vec<_>>(),
            vec![7, 3, 11, 9]
        );
        assert_eq!(
            commitment_data
                .iter()
                .map(|data| data.set_index)
                .collect::<Vec<_>>(),
            vec![0, 1, 0, 2]
        );
        assert_eq!(commitment_data[0].point_indices, vec![0, 2]);
        assert_eq!(commitment_data[1].point_indices, vec![1, 2]);
        assert_eq!(commitment_data[2].point_indices, vec![2, 0]);
        assert_eq!(commitment_data[3].point_indices, vec![1]);
        assert_eq!(commitment_data[0].evals, vec![Fp::from(72), Fp::from(71)]);
        assert_eq!(commitment_data[1].evals, vec![Fp::from(30), Fp::from(31)]);
        assert_eq!(commitment_data[2].evals, vec![Fp::from(112), Fp::from(111)]);
        assert_eq!(commitment_data[3].evals, vec![Fp::from(90)]);
        assert_eq!(
            point_sets,
            vec![
                vec![Fp::from(2), Fp::from(1)],
                vec![Fp::from(0), Fp::from(1)],
                vec![Fp::from(0)],
            ]
        );
    }

    #[test]
    fn intermediate_sets_reject_duplicate_queries() {
        let query = MyQuery {
            point: Fp::from(1),
            eval: Fp::from(2),
            commitment: 3,
        };

        assert!(construct_intermediate_sets(vec![query.clone(), query]).is_none());
    }

    prop_compose! {
        fn arb_point()(
            bytes in vec(any::<u8>(), 64)
        ) -> Fp {
            Fp::from_uniform_bytes(&<[u8; 64]>::try_from(bytes).unwrap())
        }
    }

    prop_compose! {
        fn arb_query(commitment: usize, point: Fp)(
            eval in arb_point()
        ) -> MyQuery<Fp> {
            MyQuery {
                point,
                eval,
                commitment
            }
        }
    }

    prop_compose! {
        // Mapping from column index to point index.
        fn arb_queries_inner(num_points: usize, num_cols: usize, num_queries: usize)(
            // Use a HashSet to ensure we sample distinct (column, point) queries.
            queries in hash_set(
                (
                    select((0..num_cols).collect::<Vec<_>>()),
                    select((0..num_points).collect::<Vec<_>>()),
                ),
                num_queries,
            )
        ) -> Vec<(usize, usize)> {
            queries.into_iter().collect()
        }
    }

    prop_compose! {
        fn compare_queries(
            num_points: usize,
            num_cols: usize,
            num_queries: usize,
        )(
            points_1 in vec(arb_point(), num_points),
            points_2 in vec(arb_point(), num_points),
            mapping in arb_queries_inner(num_points, num_cols, num_queries)
        )(
            queries_1 in mapping.iter().map(|(commitment, point_idx)| arb_query(*commitment, points_1[*point_idx])).collect::<Vec<_>>(),
            queries_2 in mapping.iter().map(|(commitment, point_idx)| arb_query(*commitment, points_2[*point_idx])).collect::<Vec<_>>(),
        ) -> (
            Vec<MyQuery<Fp>>,
            Vec<MyQuery<Fp>>
        ) {
            (
                queries_1,
                queries_2,
            )
        }
    }

    proptest! {
        #[test]
        fn test_intermediate_sets(
            (queries_1, queries_2) in compare_queries(8, 8, 16)
        ) {
            let (commitment_data, _point_sets) = construct_intermediate_sets(queries_1)
                .ok_or_else(|| TestCaseError::Fail("mismatched evals".into()))?;
            let set_indices = commitment_data.iter().map(|data| data.set_index).collect::<Vec<_>>();
            let point_indices = commitment_data.iter().map(|data| data.point_indices.clone()).collect::<Vec<_>>();

            // It shouldn't matter what the point or eval values are; we should get
            // the same exact point set indices and point indices again.
            let (new_commitment_data, _new_point_sets) = construct_intermediate_sets(queries_2)
                .ok_or_else(|| TestCaseError::Fail("mismatched evals".into()))?;
            let new_set_indices = new_commitment_data.iter().map(|data| data.set_index).collect::<Vec<_>>();
            let new_point_indices = new_commitment_data.iter().map(|data| data.point_indices.clone()).collect::<Vec<_>>();

            assert_eq!(set_indices, new_set_indices);
            assert_eq!(point_indices, new_point_indices);
        }
    }
}
