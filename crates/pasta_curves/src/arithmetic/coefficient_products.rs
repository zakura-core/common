//! Batched sums of challenge-product coefficient vectors.
//!
//! An inner-product-argument verifier expands its round challenges
//! `u_0, ..., u_{k-1}` into the coefficients of
//! $\mathrm{init} \cdot \prod_{i=0}^{k-1} (1 + u_{k-1-i} X^{2^i})$, a vector of
//! `2^k` scalars, and a batch verifier sums one such vector per proof. The sum
//! only has to be reduced once, when the batch is checked, so
//! [`CoefficientProducts`] keeps it in an accumulator of the field's choosing.

use alloc::vec::Vec;
use core::fmt::Debug;

use ff::Field;

/// Sums of challenge-product coefficient vectors (see the module docs).
pub trait CoefficientProducts: Field {
    /// An accumulator of coefficient vectors of one length.
    type ProductSums: Send + Sync + Debug;

    /// An empty accumulator for vectors of `2^log_len` coefficients.
    fn product_sums(log_len: usize) -> Self::ProductSums;

    /// Adds the coefficients of
    /// $\mathrm{init} \cdot \prod_{i=0}^{k-1} (1 + u_{k-1-i} X^{2^i})$, where
    /// `k = u.len()` must equal the accumulator's `log_len`.
    fn add_coefficient_products(sums: &mut Self::ProductSums, u: &[Self], init: Self);

    /// Adds every vector accumulated in `other` to `sums`.
    fn merge_product_sums(sums: &mut Self::ProductSums, other: Self::ProductSums);

    /// The reduced sum of every vector added to `sums`, lowest degree first.
    fn finish_product_sums(sums: Self::ProductSums) -> Vec<Self>;
}

/// Expands `init * prod_i (1 + u_{k-1-i} X^{2^i})` into `out`, lowest degree
/// first. Each round appends the current coefficients multiplied by the next
/// challenge, so the `2^k` coefficients cost `2^k - 1` multiplications.
pub(crate) fn expand_coefficient_products<F: Field>(u: &[F], init: F, out: &mut Vec<F>) {
    out.clear();
    out.reserve(1 << u.len());
    out.push(init);
    for u_j in u.iter().rev() {
        let len = out.len();
        for index in 0..len {
            let product = out[index] * u_j;
            out.push(product);
        }
    }
}

/// The portable [`CoefficientProducts::ProductSums`]: the field sum of the
/// coefficient vectors, with one expansion buffer reused for every vector.
#[derive(Debug)]
pub struct FieldProductSums<F> {
    log_len: usize,
    sums: Vec<F>,
    scratch: Vec<F>,
}

// The AVX2 builds sum with `Avx2ProductSums`; this accumulator remains the
// other targets' and the AVX2 tests' reference.
#[cfg_attr(
    all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2),
    allow(dead_code)
)]
impl<F: Field> FieldProductSums<F> {
    pub(crate) fn new(log_len: usize) -> Self {
        FieldProductSums {
            log_len,
            sums: alloc::vec![F::ZERO; 1 << log_len],
            scratch: Vec::new(),
        }
    }

    pub(crate) fn add(&mut self, u: &[F], init: F) {
        assert_eq!(u.len(), self.log_len, "one challenge per round");
        expand_coefficient_products(u, init, &mut self.scratch);
        for (sum, value) in self.sums.iter_mut().zip(&self.scratch) {
            *sum += value;
        }
    }

    pub(crate) fn merge(&mut self, other: Self) {
        assert_eq!(other.log_len, self.log_len, "equal-length vectors");
        for (sum, value) in self.sums.iter_mut().zip(&other.sums) {
            *sum += value;
        }
    }

    pub(crate) fn finish(self) -> Vec<F> {
        self.sums
    }
}

/// Implements [`CoefficientProducts`] for a field whose Montgomery limbs are
/// `self.0` and whose modulus is `$modulus.0`: with [`super::Avx2ProductSums`]
/// where the AVX2 backend is compiled in, [`FieldProductSums`] otherwise.
macro_rules! impl_coefficient_products {
    ($field:ident, $modulus:ident) => {
        impl crate::arithmetic::CoefficientProducts for $field {
            #[cfg(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2))]
            type ProductSums = crate::arithmetic::Avx2ProductSums<$field>;
            #[cfg(not(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2)))]
            type ProductSums = crate::arithmetic::FieldProductSums<$field>;

            fn product_sums(log_len: usize) -> Self::ProductSums {
                Self::ProductSums::new(log_len)
            }

            fn add_coefficient_products(sums: &mut Self::ProductSums, u: &[Self], init: Self) {
                #[cfg(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2))]
                sums.add::<{ $modulus.0[0] }, { $modulus.0[1] }, { $modulus.0[2] }, { $modulus.0[3] }>(
                    u,
                    init,
                    |value| value.0,
                );
                #[cfg(not(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2)))]
                sums.add(u, init);
            }

            fn merge_product_sums(sums: &mut Self::ProductSums, other: Self::ProductSums) {
                sums.merge(other);
            }

            fn finish_product_sums(sums: Self::ProductSums) -> alloc::vec::Vec<Self> {
                #[cfg(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2))]
                return sums.finish(&$modulus.0, $field);
                #[cfg(not(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2)))]
                return sums.finish();
            }
        }
    };
}
pub(crate) use impl_coefficient_products;

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use ff::Field;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::{CoefficientProducts, expand_coefficient_products};
    use crate::{Fp, Fq};

    fn naive<F: Field>(u: &[F], init: F) -> Vec<F> {
        // Coefficient of X^b: init * prod over set bits i of b of u_{k-1-i}.
        let k = u.len();
        (0..1usize << k)
            .map(|b| {
                (0..k)
                    .filter(|i| b >> i & 1 == 1)
                    .fold(init, |acc, i| acc * u[k - 1 - i])
            })
            .collect()
    }

    fn check<F: CoefficientProducts>() {
        let mut rng = XorShiftRng::from_seed([0x5c; 16]);
        let mut expanded = Vec::new();
        for k in 1..=6 {
            let u: Vec<F> = (0..k).map(|_| F::random(&mut rng)).collect();
            let init = F::random(&mut rng);
            expand_coefficient_products(&u, init, &mut expanded);
            assert_eq!(expanded, naive(&u, init), "k = {k}");
        }

        // Sums over many vectors (with extreme coefficients: -1 everywhere
        // makes every limb vector the largest canonical value), split across
        // two accumulators and merged, match field sums.
        let k = 5;
        for vectors in [0usize, 1, 2, 3, 64, 300] {
            let mut left = F::product_sums(k);
            let mut right = F::product_sums(k);
            let mut expected = alloc::vec![F::ZERO; 1 << k];
            for v in 0..vectors {
                let (u, init): (Vec<F>, F) = if v % 7 == 3 {
                    (alloc::vec![-F::ONE; k], -F::ONE)
                } else {
                    (
                        (0..k).map(|_| F::random(&mut rng)).collect(),
                        F::random(&mut rng),
                    )
                };
                for (e, c) in expected.iter_mut().zip(naive(&u, init)) {
                    *e += c;
                }
                let target = if v % 2 == 0 { &mut left } else { &mut right };
                F::add_coefficient_products(target, &u, init);
            }
            F::merge_product_sums(&mut left, right);
            assert_eq!(F::finish_product_sums(left), expected, "{vectors} vectors");
        }
    }

    #[test]
    fn coefficient_products_match_field_sums() {
        check::<Fp>();
        check::<Fq>();
    }

    /// The AVX2 accumulator equals the field sums, including at the extremes
    /// (`-1` challenges and seeds), short vectors, and merges.
    #[cfg(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2))]
    #[test]
    fn avx2_product_sums_match_field_sums() {
        fn check<F: CoefficientProducts<ProductSums = crate::arithmetic::Avx2ProductSums<F>>>() {
            let mut rng = XorShiftRng::from_seed([0x3e; 16]);
            for k in [1usize, 2, 3, 4, 5, 8, 11] {
                for vectors in [1usize, 2, 65] {
                    let mut a = F::product_sums(k);
                    let mut b = F::product_sums(k);
                    let mut reference = super::FieldProductSums::<F>::new(k);
                    for v in 0..vectors {
                        let (u, init): (Vec<F>, F) = if v % 5 == 1 {
                            (alloc::vec![-F::ONE; k], -F::ONE)
                        } else {
                            (
                                (0..k).map(|_| F::random(&mut rng)).collect(),
                                F::random(&mut rng),
                            )
                        };
                        F::add_coefficient_products(
                            if v % 3 == 0 { &mut a } else { &mut b },
                            &u,
                            init,
                        );
                        reference.add(&u, init);
                    }
                    F::merge_product_sums(&mut a, b);
                    assert_eq!(
                        F::finish_product_sums(a),
                        reference.finish(),
                        "k = {k}, {vectors} vectors"
                    );
                }
            }
        }
        check::<Fp>();
        check::<Fq>();
    }
}
