//! Contains utilities for performing arithmetic over univariate polynomials in
//! various forms, including computing commitments to them and provably opening
//! the committed polynomials at arbitrary points.

use crate::arithmetic::{compute_inner_product, parallelize};
use crate::plonk::Assigned;

use group::ff::{BatchInvert, Field};
use pasta_curves::{deferred::DeferredField, pallas, vesta};

use std::any::{Any, TypeId};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::{Add, Deref, DerefMut, Index, IndexMut, Mul, RangeFrom, RangeFull};

pub mod commitment;
mod domain;
mod evaluator;
pub mod multiopen;

pub use domain::*;
pub(crate) use evaluator::*;

fn power_vector<F: Field>(point: F, len: usize) -> Vec<F> {
    let mut powers = Vec::with_capacity(len);
    if len == 0 {
        return powers;
    }

    powers.push(F::ONE);
    if len == 1 {
        return powers;
    }

    let mut power = point;
    powers.push(power);
    for _ in 2..len {
        power *= point;
        powers.push(power);
    }
    powers
}

fn evaluate_polynomial_deferred<F: Field + 'static, T: DeferredField + 'static>(
    polynomial: &dyn Any,
    powers: &dyn Any,
) -> F {
    let polynomial = polynomial
        .downcast_ref::<Polynomial<T, Coeff>>()
        .expect("the polynomial field was checked before conversion");
    let powers = powers
        .downcast_ref::<Vec<T>>()
        .expect("the power-vector field was checked before conversion");
    let (constant, coefficients) = polynomial
        .split_first()
        .expect("a polynomial evaluation has at least one coefficient");
    let value = T::inner_product(coefficients, &powers[1..]) + constant;
    let value: Box<dyn Any> = Box::new(value);
    *value
        .downcast::<F>()
        .expect("the evaluation field matches the polynomial field")
}

// A `Vec` is required for safe runtime downcasting to the Pasta field.
#[allow(clippy::ptr_arg)]
fn evaluate_polynomial_with_powers<F: Field + 'static>(
    polynomial: &Polynomial<F, Coeff>,
    powers: &Vec<F>,
) -> F {
    assert_eq!(polynomial.len(), powers.len());
    if polynomial.is_empty() {
        return F::ZERO;
    }

    if TypeId::of::<F>() == TypeId::of::<pallas::Base>() {
        evaluate_polynomial_deferred::<F, pallas::Base>(polynomial, powers)
    } else if TypeId::of::<F>() == TypeId::of::<vesta::Base>() {
        evaluate_polynomial_deferred::<F, vesta::Base>(polynomial, powers)
    } else {
        compute_inner_product(&polynomial[1..], &powers[1..]) + polynomial[0]
    }
}

/// This is an error that could occur during proving or circuit synthesis.
// TODO: these errors need to be cleaned up
#[derive(Debug)]
pub enum Error {
    /// OpeningProof is not well-formed
    OpeningError,
    /// Caller needs to re-sample a point
    SamplingError,
}

/// The basis over which a polynomial is described.
pub trait Basis: Copy + Debug + Send + Sync {}

/// The polynomial is defined as coefficients
#[derive(Clone, Copy, Debug)]
pub struct Coeff;
impl Basis for Coeff {}

/// The polynomial is defined as coefficients of Lagrange basis polynomials
#[derive(Clone, Copy, Debug)]
pub struct LagrangeCoeff;
impl Basis for LagrangeCoeff {}

/// The polynomial is defined as coefficients of Lagrange basis polynomials in
/// an extended size domain which supports multiplication
#[derive(Clone, Copy, Debug)]
pub struct ExtendedLagrangeCoeff;
impl Basis for ExtendedLagrangeCoeff {}

/// Represents a univariate polynomial defined over a field and a particular
/// basis.
#[derive(Clone, Debug)]
pub struct Polynomial<F, B> {
    values: Vec<F>,
    _marker: PhantomData<B>,
}

impl<F, B> Index<usize> for Polynomial<F, B> {
    type Output = F;

    fn index(&self, index: usize) -> &F {
        self.values.index(index)
    }
}

impl<F, B> IndexMut<usize> for Polynomial<F, B> {
    fn index_mut(&mut self, index: usize) -> &mut F {
        self.values.index_mut(index)
    }
}

impl<F, B> Index<RangeFrom<usize>> for Polynomial<F, B> {
    type Output = [F];

    fn index(&self, index: RangeFrom<usize>) -> &[F] {
        self.values.index(index)
    }
}

impl<F, B> IndexMut<RangeFrom<usize>> for Polynomial<F, B> {
    fn index_mut(&mut self, index: RangeFrom<usize>) -> &mut [F] {
        self.values.index_mut(index)
    }
}

impl<F, B> Index<RangeFull> for Polynomial<F, B> {
    type Output = [F];

    fn index(&self, index: RangeFull) -> &[F] {
        self.values.index(index)
    }
}

impl<F, B> IndexMut<RangeFull> for Polynomial<F, B> {
    fn index_mut(&mut self, index: RangeFull) -> &mut [F] {
        self.values.index_mut(index)
    }
}

impl<F, B> Deref for Polynomial<F, B> {
    type Target = [F];

    fn deref(&self) -> &[F] {
        &self.values[..]
    }
}

impl<F, B> DerefMut for Polynomial<F, B> {
    fn deref_mut(&mut self) -> &mut [F] {
        &mut self.values[..]
    }
}

impl<F, B> Polynomial<F, B> {
    /// Iterate over the values, which are either in coefficient or evaluation
    /// form depending on the basis `B`.
    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.values.iter()
    }

    /// Iterate over the values mutably, which are either in coefficient or
    /// evaluation form depending on the basis `B`.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut F> {
        self.values.iter_mut()
    }

    /// Gets the size of this polynomial in terms of the number of
    /// coefficients used to describe it.
    pub fn num_coeffs(&self) -> usize {
        self.values.len()
    }
}

pub(crate) fn batch_invert_assigned<F: Field>(
    assigned: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
) -> Vec<Polynomial<F, LagrangeCoeff>> {
    let mut assigned_denominators: Vec<_> = assigned
        .iter()
        .map(|f| {
            f.iter()
                .map(|value| value.denominator())
                .collect::<Vec<_>>()
        })
        .collect();

    assigned_denominators
        .iter_mut()
        .flat_map(|f| {
            f.iter_mut()
                // If the denominator is trivial, we can skip it, reducing the
                // size of the batch inversion.
                .filter_map(|d| d.as_mut())
        })
        .batch_invert();

    assigned
        .iter()
        .zip(assigned_denominators)
        .map(|(poly, inv_denoms)| poly.invert(inv_denoms.into_iter().map(|d| d.unwrap_or(F::ONE))))
        .collect()
}

impl<F: Field> Polynomial<Assigned<F>, LagrangeCoeff> {
    pub(crate) fn invert(
        &self,
        inv_denoms: impl ExactSizeIterator<Item = F>,
    ) -> Polynomial<F, LagrangeCoeff> {
        assert_eq!(inv_denoms.len(), self.values.len());
        Polynomial {
            values: self
                .values
                .iter()
                .zip(inv_denoms)
                .map(|(a, inv_den)| a.numerator() * inv_den)
                .collect(),
            _marker: self._marker,
        }
    }
}

impl<'a, F: Field, B: Basis> Add<&'a Polynomial<F, B>> for Polynomial<F, B> {
    type Output = Polynomial<F, B>;

    fn add(mut self, rhs: &'a Polynomial<F, B>) -> Polynomial<F, B> {
        parallelize(&mut self.values, |lhs, start| {
            for (lhs, rhs) in lhs.iter_mut().zip(rhs.values[start..].iter()) {
                *lhs += *rhs;
            }
        });

        self
    }
}

impl<F: Field> Polynomial<F, LagrangeCoeff> {
    /// Rotates the values in a Lagrange basis polynomial by [`Rotation`].
    pub fn rotate(&self, rotation: Rotation) -> Polynomial<F, LagrangeCoeff> {
        let mut values = self.values.clone();
        if rotation.0 < 0 {
            values.rotate_right((-rotation.0) as usize);
        } else {
            values.rotate_left(rotation.0 as usize);
        }
        Polynomial {
            values,
            _marker: PhantomData,
        }
    }

    /// Copies the specified chunk of the rotated polynomial into `output`.
    ///
    /// Equivalent to:
    /// ```ignore
    /// output.copy_from_slice(
    ///     self.rotate(rotation)
    ///         .chunks(chunk_size)
    ///         .nth(chunk_index)
    ///         .unwrap(),
    /// )
    /// ```
    #[cfg(test)]
    fn copy_rotated_chunk(
        &self,
        rotation: Rotation,
        chunk_size: usize,
        chunk_index: usize,
        output: &mut [F],
    ) {
        self.copy_rotated_chunk_helper(
            rotation.0 < 0,
            rotation.0.unsigned_abs() as usize,
            chunk_size,
            chunk_index,
            output,
        )
    }
}

impl<F: Clone + Copy, B> Polynomial<F, B> {
    #[cfg(test)]
    fn copy_rotated_chunk_helper(
        &self,
        rotation_is_negative: bool,
        rotation_abs: usize,
        chunk_size: usize,
        chunk_index: usize,
        output: &mut [F],
    ) {
        assert!(rotation_abs <= self.len());

        // A positive rotation starts at `rotation_abs`; a negative rotation
        // starts that far before the end.
        let mid = if rotation_is_negative {
            self.len() - rotation_abs
        } else {
            rotation_abs
        };
        let unwrapped_start = mid + chunk_size * chunk_index;
        let source_start = if unwrapped_start >= self.len() {
            unwrapped_start - self.len()
        } else {
            unwrapped_start
        };

        let first_len = output.len().min(self.len() - source_start);
        output[..first_len].copy_from_slice(&self.values[source_start..][..first_len]);
        let remaining = output.len() - first_len;
        output[first_len..].copy_from_slice(&self.values[..remaining]);
    }
}

impl<F: Field, B: Basis> Mul<F> for Polynomial<F, B> {
    type Output = Polynomial<F, B>;

    fn mul(mut self, rhs: F) -> Polynomial<F, B> {
        parallelize(&mut self.values, |lhs, _| {
            for lhs in lhs.iter_mut() {
                *lhs *= rhs;
            }
        });

        self
    }
}

/// Describes the relative rotation of a vector. Negative numbers represent
/// reverse (leftmost) rotations and positive numbers represent forward (rightmost)
/// rotations. Zero represents no rotation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Rotation(pub i32);

impl Rotation {
    /// The current location in the evaluation domain
    pub fn cur() -> Rotation {
        Rotation(0)
    }

    /// The previous location in the evaluation domain
    pub fn prev() -> Rotation {
        Rotation(-1)
    }

    /// The next location in the evaluation domain
    pub fn next() -> Rotation {
        Rotation(1)
    }
}

#[cfg(test)]
mod tests {
    use crate::arithmetic::eval_polynomial;
    use ff::Field;
    use pasta_curves::{pallas, vesta};
    use rand::rng;
    use std::marker::PhantomData;

    use super::{
        Coeff, EvaluationDomain, Polynomial, Rotation, evaluate_polynomial_with_powers,
        power_vector,
    };

    fn check_evaluate_polynomial_with_powers<F: Field + From<u64>>() {
        let point = F::from(7);
        for len in [0, 1, 2, 3, 31, 32, 2_048] {
            let polynomial = Polynomial::<_, Coeff> {
                values: (0..len)
                    .map(|coefficient| F::from((coefficient + 3) as u64))
                    .collect(),
                _marker: PhantomData,
            };
            let powers = power_vector(point, len);
            assert_eq!(
                evaluate_polynomial_with_powers(&polynomial, &powers),
                eval_polynomial(&polynomial, point),
            );
        }
    }

    #[test]
    fn polynomial_evaluation_with_powers_matches_horner() {
        check_evaluate_polynomial_with_powers::<pallas::Base>();
        check_evaluate_polynomial_with_powers::<vesta::Base>();
    }

    #[test]
    fn test_copy_rotated_chunk() {
        let k = 11;
        let domain = EvaluationDomain::<pallas::Base>::new(1, k);

        // Create a random polynomial.
        let mut poly = domain.empty_lagrange();
        for coefficient in poly.iter_mut() {
            *coefficient = pallas::Base::random(&mut rng());
        }

        // Pick a chunk size that is guaranteed to not be a multiple of the polynomial
        // length.
        let chunk_size = 7;

        for rotation in [
            Rotation(-6),
            Rotation::prev(),
            Rotation::cur(),
            Rotation::next(),
            Rotation(12),
        ] {
            for (chunk_index, chunk) in poly.rotate(rotation).chunks(chunk_size).enumerate() {
                let mut actual = vec![pallas::Base::ZERO; chunk.len()];
                poly.copy_rotated_chunk(rotation, chunk_size, chunk_index, &mut actual);
                assert_eq!(actual, chunk);
            }
        }
    }
}
