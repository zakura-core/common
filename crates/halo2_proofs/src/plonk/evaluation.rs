use std::{
    any::{Any, TypeId},
    marker::PhantomData,
};

use ff::Field;
use maybe_rayon::prelude::*;
use pasta_curves::{deferred::DeferredField, pallas, vesta};

use crate::{
    arithmetic::eval_polynomial,
    poly::{Coeff, Polynomial, Rotation},
};

#[derive(Clone, Copy)]
pub(super) enum EvaluationPoint<F: Field> {
    Current,
    Next,
    Previous,
    Last,
    Other(F),
}

impl<F: Field> EvaluationPoint<F> {
    pub(super) fn from_rotation(
        rotation: Rotation,
        blinding_factors: usize,
        other: impl FnOnce() -> F,
    ) -> Self {
        match rotation.0 {
            0 => Self::Current,
            1 => Self::Next,
            -1 => Self::Previous,
            rotation if rotation == -((blinding_factors + 1) as i32) => Self::Last,
            _ => Self::Other(other()),
        }
    }
}

#[derive(Clone, Copy)]
pub(super) struct EvaluationQuery<'a, F: Field> {
    pub(super) polynomial: &'a Polynomial<F, Coeff>,
    pub(super) point: EvaluationPoint<F>,
}

const POINT_COUNT: usize = 4;
const LAST_POINT_INDEX: usize = 3;
const MIN_PROOFS_FOR_LAST_POINT_TABLE: usize = 2;

struct PowerTables<F: Field> {
    points: [F; POINT_COUNT],
    powers: [Option<Vec<F>>; POINT_COUNT],
}

impl<F: Field> PowerTables<F> {
    fn new(points: [F; POINT_COUNT], polynomial_len: usize, num_proofs: usize) -> Self {
        let build_last = num_proofs >= MIN_PROOFS_FOR_LAST_POINT_TABLE;
        let powers = points
            .into_par_iter()
            .enumerate()
            .map(|(index, point)| {
                if index == LAST_POINT_INDEX && !build_last {
                    None
                } else {
                    let mut powers = Vec::with_capacity(polynomial_len);
                    let mut power = F::ONE;
                    for _ in 0..polynomial_len {
                        powers.push(power);
                        power *= point;
                    }
                    Some(powers)
                }
            })
            .collect::<Vec<_>>()
            .try_into()
            .expect("the fixed evaluation-point count is preserved");

        Self { points, powers }
    }

    fn point_index(point: EvaluationPoint<F>) -> Option<usize> {
        match point {
            EvaluationPoint::Current => Some(0),
            EvaluationPoint::Next => Some(1),
            EvaluationPoint::Previous => Some(2),
            EvaluationPoint::Last => Some(LAST_POINT_INDEX),
            EvaluationPoint::Other(_) => None,
        }
    }

    fn point(&self, point: EvaluationPoint<F>) -> F {
        match Self::point_index(point) {
            Some(index) => self.points[index],
            None => match point {
                EvaluationPoint::Other(point) => point,
                _ => unreachable!(),
            },
        }
    }
}

pub(super) struct PolynomialEvaluator<F: Field> {
    inner: PolynomialEvaluatorInner<F>,
}

enum PolynomialEvaluatorInner<F: Field> {
    Horner {
        points: [F; POINT_COUNT],
    },
    Pallas {
        tables: PowerTables<pallas::Base>,
        marker: PhantomData<F>,
    },
    Vesta {
        tables: PowerTables<vesta::Base>,
        marker: PhantomData<F>,
    },
}

impl<F: Field> PolynomialEvaluator<F> {
    pub(super) fn new(points: [F; POINT_COUNT], polynomial_len: usize, num_proofs: usize) -> Self {
        if TypeId::of::<F>() == TypeId::of::<pallas::Base>() {
            Self {
                inner: PolynomialEvaluatorInner::Pallas {
                    tables: PowerTables::new(
                        convert_points::<F, pallas::Base>(points),
                        polynomial_len,
                        num_proofs,
                    ),
                    marker: PhantomData,
                },
            }
        } else if TypeId::of::<F>() == TypeId::of::<vesta::Base>() {
            Self {
                inner: PolynomialEvaluatorInner::Vesta {
                    tables: PowerTables::new(
                        convert_points::<F, vesta::Base>(points),
                        polynomial_len,
                        num_proofs,
                    ),
                    marker: PhantomData,
                },
            }
        } else {
            Self {
                inner: PolynomialEvaluatorInner::Horner { points },
            }
        }
    }

    pub(super) fn evaluate(&self, queries: &[EvaluationQuery<'_, F>]) -> Vec<F> {
        match &self.inner {
            PolynomialEvaluatorInner::Horner { points } => queries
                .into_par_iter()
                .map(|query| {
                    let point = match PowerTables::<F>::point_index(query.point) {
                        Some(index) => points[index],
                        None => match query.point {
                            EvaluationPoint::Other(point) => point,
                            _ => unreachable!(),
                        },
                    };
                    eval_polynomial(query.polynomial, point)
                })
                .collect(),
            PolynomialEvaluatorInner::Pallas { tables, .. } => {
                evaluate_deferred::<F, pallas::Base>(tables, queries)
            }
            PolynomialEvaluatorInner::Vesta { tables, .. } => {
                evaluate_deferred::<F, vesta::Base>(tables, queries)
            }
        }
    }
}

fn convert_points<F: Field, T: Field>(points: [F; POINT_COUNT]) -> [T; POINT_COUNT] {
    points.map(|point| {
        *(&point as &dyn Any)
            .downcast_ref::<T>()
            .expect("the evaluation-point field was checked before conversion")
    })
}

fn evaluate_deferred<F: Field, T: DeferredField + 'static>(
    tables: &PowerTables<T>,
    queries: &[EvaluationQuery<'_, F>],
) -> Vec<F> {
    let values = queries
        .into_par_iter()
        .map(|query| {
            let polynomial = (query.polynomial as &dyn Any)
                .downcast_ref::<Polynomial<T, Coeff>>()
                .expect("the polynomial field matches its power tables");
            let point = convert_point::<F, T>(query.point);
            match PowerTables::<T>::point_index(point)
                .and_then(|point_index| tables.powers[point_index].as_deref())
            {
                Some(powers) => deferred_inner_product(polynomial, powers),
                None => eval_polynomial(polynomial, tables.point(point)),
            }
        })
        .collect::<Vec<T>>();

    let values: Box<dyn Any> = Box::new(values);
    match values.downcast::<Vec<F>>() {
        Ok(values) => *values,
        Err(_) => unreachable!("the output field was checked before evaluation"),
    }
}

fn convert_point<F: Field, T: Field>(point: EvaluationPoint<F>) -> EvaluationPoint<T> {
    match point {
        EvaluationPoint::Current => EvaluationPoint::Current,
        EvaluationPoint::Next => EvaluationPoint::Next,
        EvaluationPoint::Previous => EvaluationPoint::Previous,
        EvaluationPoint::Last => EvaluationPoint::Last,
        EvaluationPoint::Other(point) => EvaluationPoint::Other(
            *(&point as &dyn Any)
                .downcast_ref::<T>()
                .expect("the evaluation-point field was checked before conversion"),
        ),
    }
}

fn deferred_inner_product<F: DeferredField>(polynomial: &[F], powers: &[F]) -> F {
    if let Some(value) = crate::arithmetic::batch::inner_product(polynomial, powers) {
        return value;
    }
    F::inner_product(polynomial, powers)
}

#[cfg(test)]
mod tests {
    use super::{
        EvaluationPoint, EvaluationQuery, LAST_POINT_INDEX, PolynomialEvaluator, PowerTables,
        deferred_inner_product,
    };
    use crate::{arithmetic::eval_polynomial, poly::EvaluationDomain};
    use ff::Field;
    use pasta_curves::pallas;
    use rand::{SeedableRng, rngs::StdRng};

    #[test]
    fn deferred_evaluation_matches_horner() {
        let mut rng = StdRng::seed_from_u64(0x706f_6c79_6576_616c);
        for len in [1, 2, 3, 31, 32, 2_048] {
            let polynomial = (0..len)
                .map(|_| pallas::Base::random(&mut rng))
                .collect::<Vec<_>>();
            let powers = (0..len)
                .scan(pallas::Base::ONE, |power, _| {
                    let current = *power;
                    *power *= pallas::Base::from(17);
                    Some(current)
                })
                .collect::<Vec<_>>();
            let expected = eval_polynomial(&polynomial, pallas::Base::from(17));
            assert_eq!(deferred_inner_product(&polynomial, &powers), expected);
        }

        let domain = EvaluationDomain::<pallas::Base>::new(4, 9);
        let points = [
            pallas::Base::from(3),
            pallas::Base::from(5),
            pallas::Base::from(7),
            pallas::Base::from(11),
        ];
        let polynomials = (0..10)
            .map(|_| {
                domain.coeff_from_vec(
                    (0..(1 << 9))
                        .map(|_| pallas::Base::random(&mut rng))
                        .collect(),
                )
            })
            .collect::<Vec<_>>();
        let evaluator = PolynomialEvaluator::new(points, 1 << 9, 1);
        let queries = polynomials
            .iter()
            .enumerate()
            .map(|(index, polynomial)| EvaluationQuery {
                polynomial,
                point: match index % 5 {
                    0 => EvaluationPoint::Current,
                    1 => EvaluationPoint::Next,
                    2 => EvaluationPoint::Previous,
                    3 => EvaluationPoint::Last,
                    _ => EvaluationPoint::Other(pallas::Base::from(13)),
                },
            })
            .collect::<Vec<_>>();
        let actual = evaluator.evaluate(&queries);
        for (query, actual) in queries.iter().zip(actual.iter().copied()) {
            assert_eq!(
                actual,
                eval_polynomial(query.polynomial, point_value(query.point, points)),
            );
        }

        // Combining independently evaluated query batches must preserve the
        // exact scalar order consumed by the transcript.
        let separately = queries
            .chunks(3)
            .flat_map(|batch| evaluator.evaluate(batch))
            .collect::<Vec<_>>();
        assert_eq!(actual, separately);
    }

    #[test]
    fn last_point_table_is_adaptive() {
        let points = [
            pallas::Base::from(3),
            pallas::Base::from(5),
            pallas::Base::from(7),
            pallas::Base::from(11),
        ];
        let one_proof = PowerTables::new(points, 1 << 9, 1);
        assert!(one_proof.powers[LAST_POINT_INDEX].is_none());

        let two_proofs = PowerTables::new(points, 1 << 9, 2);
        assert!(two_proofs.powers[LAST_POINT_INDEX].is_some());
    }

    fn point_value(
        point: EvaluationPoint<pallas::Base>,
        points: [pallas::Base; 4],
    ) -> pallas::Base {
        match point {
            EvaluationPoint::Current => points[0],
            EvaluationPoint::Next => points[1],
            EvaluationPoint::Previous => points[2],
            EvaluationPoint::Last => points[3],
            EvaluationPoint::Other(point) => point,
        }
    }
}
