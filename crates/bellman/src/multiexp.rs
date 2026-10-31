use super::multicore::{Waiter, Worker};
use ff::PrimeField;
use group::{
    Curve,
    prime::{PrimeCurve, PrimeCurveAffine},
};
use std::io;
use std::iter;
use std::ops::AddAssign;
use std::sync::Arc;

#[cfg(feature = "multicore")]
use rayon::prelude::*;

#[cfg(not(feature = "multicore"))]
use crate::multicore::FakeParallelIterator;

use super::{SynthesisError, le_bit};

/// An object that builds a source of bases.
pub trait SourceBuilder<G: PrimeCurveAffine>: Send + Sync + 'static + Clone {
    type Source: Source<G>;

    fn build(self) -> Self::Source;
}

/// A source of bases, like an iterator.
pub trait Source<G: PrimeCurveAffine> {
    fn next(&mut self) -> Result<&G, SynthesisError>;

    /// Skips `amt` elements from the source, avoiding deserialization.
    fn skip(&mut self, amt: usize) -> Result<(), SynthesisError>;
}

pub trait AddAssignFromSource: PrimeCurve {
    /// Parses the element from the source. Fails if the point is at infinity.
    fn add_assign_from_source<S: Source<<Self as Curve>::Affine>>(
        &mut self,
        source: &mut S,
    ) -> Result<(), SynthesisError> {
        AddAssign::<&<Self as Curve>::Affine>::add_assign(self, source.next()?);
        Ok(())
    }
}
impl<G> AddAssignFromSource for G where G: PrimeCurve {}

impl<G: PrimeCurveAffine> SourceBuilder<G> for (Arc<Vec<G>>, usize) {
    type Source = (Arc<Vec<G>>, usize);

    fn build(self) -> (Arc<Vec<G>>, usize) {
        (self.0.clone(), self.1)
    }
}

impl<G: PrimeCurveAffine> Source<G> for (Arc<Vec<G>>, usize) {
    fn next(&mut self) -> Result<&G, SynthesisError> {
        if self.0.len() <= self.1 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "expected more bases from source",
            )
            .into());
        }

        if self.0[self.1].is_identity().into() {
            return Err(SynthesisError::UnexpectedIdentity);
        }

        let ret = &self.0[self.1];
        self.1 += 1;

        Ok(ret)
    }

    fn skip(&mut self, amt: usize) -> Result<(), SynthesisError> {
        if self.0.len() <= self.1 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "expected more bases from source",
            )
            .into());
        }

        self.1 += amt;

        Ok(())
    }
}

pub trait QueryDensity {
    /// Returns whether the base exists.
    type Iter: Iterator<Item = bool>;

    fn iter(self) -> Self::Iter;
    fn get_query_size(self) -> Option<usize>;
}

#[derive(Clone)]
pub struct FullDensity;

impl AsRef<FullDensity> for FullDensity {
    fn as_ref(&self) -> &FullDensity {
        self
    }
}

impl<'a> QueryDensity for &'a FullDensity {
    type Iter = iter::Repeat<bool>;

    fn iter(self) -> Self::Iter {
        iter::repeat(true)
    }

    fn get_query_size(self) -> Option<usize> {
        None
    }
}

/// Tracks which bases a query uses, one bit per base.
pub struct DensityTracker {
    /// The bits, 64 per word, starting with the least-significant bit of `words[0]`.
    words: Vec<u64>,
    len: usize,
}

impl<'a> QueryDensity for &'a DensityTracker {
    type Iter = Box<dyn 'a + Iterator<Item = bool>>;

    fn iter(self) -> Self::Iter {
        Box::new((0..self.len).map(|idx| (self.words[idx / 64] >> (idx % 64)) & 1 == 1))
    }

    fn get_query_size(self) -> Option<usize> {
        Some(self.len)
    }
}

impl Default for DensityTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl DensityTracker {
    pub fn new() -> DensityTracker {
        DensityTracker {
            words: Vec::new(),
            len: 0,
        }
    }

    pub fn add_element(&mut self) {
        if self.len.is_multiple_of(64) {
            self.words.push(0);
        }
        self.len += 1;
    }

    /// Marks base `idx` as used.
    ///
    /// # Panics
    ///
    /// Panics if `idx` has not been added with `add_element`.
    pub fn inc(&mut self, idx: usize) {
        assert!(idx < self.len, "density index out of range");
        self.words[idx / 64] |= 1 << (idx % 64);
    }

    pub fn get_total_density(&self) -> usize {
        self.words
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum()
    }
}

enum ChunkedExponent {
    Zero,
    One,
    Chunks(Vec<u64>),
}

/// An exponent
pub enum Exponent<F: PrimeField> {
    Zero,
    One,
    /// The canonical little-endian representation of any other exponent.
    Repr(F::Repr),
}

impl<F: PrimeField> From<&F> for Exponent<F> {
    fn from(exp: &F) -> Self {
        if exp.is_zero_vartime() {
            Exponent::Zero
        } else if exp == &F::ONE {
            Exponent::One
        } else {
            Exponent::Repr(exp.to_repr())
        }
    }
}

impl<F: PrimeField> From<F> for Exponent<F> {
    fn from(exp: F) -> Self {
        (&exp).into()
    }
}

impl<F: PrimeField> Exponent<F> {
    /// Splits the exponent into `c`-bit windows, starting with the least
    /// significant, covering its `F::NUM_BITS` bits.
    fn chunks(&self, c: usize) -> ChunkedExponent {
        match self {
            Self::Zero => ChunkedExponent::Zero,
            Self::One => ChunkedExponent::One,
            Self::Repr(repr) => ChunkedExponent::Chunks(
                (0..F::NUM_BITS as usize)
                    .step_by(c)
                    .map(|start| window(repr.as_ref(), start, c))
                    .collect(),
            ),
        }
    }
}

/// The `c`-bit window of the little-endian `repr` that starts at bit `start`.
/// Bits past the end of `repr` read as zero.
fn window(repr: &[u8], start: usize, c: usize) -> u64 {
    debug_assert!(c < 64);
    (start..(start + c).min(repr.len() * 8))
        .rev()
        .fold(0, |acc, bit| (acc << 1) | u64::from(le_bit(repr, bit)))
}

fn multiexp_inner<Q, D, G, S>(
    bases: S,
    density_map: D,
    exponents: Arc<Vec<Exponent<G::Scalar>>>,
    c: u32,
) -> Result<G, SynthesisError>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: PrimeCurve,
    G::Scalar: PrimeField,
    S: SourceBuilder<<G as Curve>::Affine>,
{
    // Perform this region of the multiexp
    let this = move |bases: S,
                     density_map: D,
                     exponents: Arc<Vec<ChunkedExponent>>,
                     chunk: usize|
          -> Result<_, SynthesisError> {
        // Accumulate the result
        let mut acc = G::identity();

        // Build a source for the bases
        let mut bases = bases.build();

        // Create space for the buckets
        let mut buckets = vec![G::identity(); (1 << c) - 1];

        // only the first round uses this
        let handle_trivial = chunk == 0;

        // Sort the bases into buckets
        for (exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
            if density {
                match exp {
                    ChunkedExponent::Zero => bases.skip(1)?,
                    ChunkedExponent::One => {
                        if handle_trivial {
                            acc.add_assign_from_source(&mut bases)?;
                        } else {
                            bases.skip(1)?;
                        }
                    }
                    ChunkedExponent::Chunks(chunks) => {
                        let exp = chunks[chunk];

                        if exp != 0 {
                            (&mut buckets[(exp - 1) as usize])
                                .add_assign_from_source(&mut bases)?;
                        } else {
                            bases.skip(1)?;
                        }
                    }
                }
            }
        }

        // Summation by parts
        // e.g. 3a + 2b + 1c = a +
        //                    (a) + b +
        //                    ((a) + b) + c
        let mut running_sum = G::identity();
        for exp in buckets.into_iter().rev() {
            running_sum.add_assign(&exp);
            acc.add_assign(&running_sum);
        }

        Ok(acc)
    };

    // Split the exponents into chunks.
    let exponents = Arc::new(
        exponents
            .iter()
            .map(|exp| exp.chunks(c as usize))
            .collect::<Vec<_>>(),
    );

    let parts = (0..G::Scalar::NUM_BITS)
        .into_par_iter()
        .step_by(c as usize)
        .enumerate()
        .map(|(chunk, _)| this(bases.clone(), density_map.clone(), exponents.clone(), chunk))
        .collect::<Vec<Result<_, _>>>();

    parts
        .into_iter()
        .rev()
        .try_fold(G::identity(), |acc, part| {
            part.map(|part| (0..c).fold(acc, |acc, _| acc.double()) + part)
        })
}

/// Perform multi-exponentiation. The caller is responsible for ensuring the
/// query size is the same as the number of exponents.
pub fn multiexp<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<Exponent<G::Scalar>>>,
) -> Waiter<Result<G, SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: PrimeCurve,
    G::Scalar: PrimeField,
    S: SourceBuilder<<G as Curve>::Affine>,
{
    let c = if exponents.len() < 32 {
        3u32
    } else {
        (f64::from(exponents.len() as u32)).ln().ceil() as u32
    };

    if let Some(query_size) = density_map.as_ref().get_query_size() {
        // If the density map has a known query size, it should not be
        // inconsistent with the number of exponents.

        assert!(query_size == exponents.len());
    }

    pool.compute(move || multiexp_inner(bases, density_map, exponents, c))
}

#[cfg(feature = "pairing")]
#[test]
fn test_with_bls12() {
    fn naive_multiexp<G: PrimeCurve>(
        bases: Arc<Vec<<G as Curve>::Affine>>,
        exponents: Arc<Vec<G::Scalar>>,
    ) -> G {
        assert_eq!(bases.len(), exponents.len());

        let mut acc = G::identity();

        for (base, exp) in bases.iter().zip(exponents.iter()) {
            AddAssign::<&G>::add_assign(&mut acc, &(*base * *exp));
        }

        acc
    }

    use bls12_381::{Bls12, Scalar};
    use ff::Field;
    use group::{Curve, Group};
    use pairing::Engine;

    const SAMPLES: usize = 1 << 14;

    let mut rng = rand::rng();
    let v = Arc::new(
        (0..SAMPLES)
            .map(|_| Scalar::random(&mut rng))
            .collect::<Vec<_>>(),
    );
    let v_bits = Arc::new(v.iter().map(|e| e.into()).collect::<Vec<_>>());
    let g = Arc::new(
        (0..SAMPLES)
            .map(|_| <Bls12 as Engine>::G1::random(&mut rng).to_affine())
            .collect::<Vec<_>>(),
    );

    let naive: <Bls12 as Engine>::G1 = naive_multiexp(g.clone(), v);

    let pool = Worker::new();
    let fast = multiexp(&pool, (g, 0), FullDensity, v_bits).wait().unwrap();

    assert_eq!(naive, fast);
}
