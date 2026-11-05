//! Batched sums of challenge-product coefficient vectors.
//!
//! An inner-product-argument verifier expands its round challenges
//! `u_0, ..., u_{k-1}` into the coefficients of
//! $\mathrm{init} \cdot \prod_{i=0}^{k-1} (1 + u_{k-1-i} X^{2^i})$, a vector of
//! `2^k` scalars (the coefficient of `X^b` is `init` times the `u_{k-1-i}` for
//! the set bits `i` of `b`), and a batch verifier sums one such vector per
//! proof. [`CoefficientProducts::sum_coefficient_products`] computes that sum
//! for a whole batch at once.

use alloc::vec::Vec;

use ff::Field;

/// Sums of challenge-product coefficient vectors (see the module docs).
pub trait CoefficientProducts: Field {
    /// Returns the sum, over `(u, init)` in `products`, of the coefficients of
    /// $\mathrm{init} \cdot \prod_{i=0}^{k-1} (1 + u_{k-1-i} X^{2^i})$, lowest
    /// degree first. Every `u` must have the same length `k`; an empty
    /// `products` returns an empty vector.
    fn sum_coefficient_products(products: &[(Vec<Self>, Self)]) -> Vec<Self>;
}

/// Expands the coefficients of one product into `out`, replacing its
/// contents. Each round appends the coefficients so far multiplied by the
/// next challenge, so the `2^k` coefficients cost `2^k - 1` multiplications.
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

/// The portable sum: each product is expanded into one reused buffer and
/// added into the sums.
pub(crate) fn sum_coefficient_products_scalar<F: Field>(products: &[(Vec<F>, F)]) -> Vec<F> {
    let Some((first, _)) = products.first() else {
        return Vec::new();
    };
    let mut sums = alloc::vec![F::ZERO; 1 << first.len()];
    let mut expanded = Vec::new();
    for (u, init) in products {
        assert_eq!(u.len(), first.len(), "one challenge per round");
        expand_coefficient_products(u, *init, &mut expanded);
        for (sum, value) in sums.iter_mut().zip(&expanded) {
            *sum += value;
        }
    }
    sums
}

/// Implements [`CoefficientProducts`] for a field whose Montgomery limbs are
/// `self.0` and whose modulus is `$modulus.0`: the AVX2 sum where it is
/// compiled in, the portable one otherwise.
macro_rules! impl_coefficient_products {
    ($field:ident, $modulus:ident) => {
        impl crate::arithmetic::CoefficientProducts for $field {
            fn sum_coefficient_products(
                products: &[(alloc::vec::Vec<Self>, Self)],
            ) -> alloc::vec::Vec<Self> {
                #[cfg(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2))]
                return crate::arithmetic::avx2_products::sum_coefficient_products::<
                    $field,
                    { $modulus.0[0] },
                    { $modulus.0[1] },
                    { $modulus.0[2] },
                    { $modulus.0[3] },
                >(products, &$modulus.0, |value| value.0, $field);
                #[cfg(not(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2)))]
                return crate::arithmetic::coefficient_products::sum_coefficient_products_scalar(
                    products,
                );
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

    use super::{
        CoefficientProducts, expand_coefficient_products, sum_coefficient_products_scalar,
    };
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

    /// The expansion matches the definition, and the field's sum (the AVX2
    /// sum where it is compiled in) matches summed naive expansions, for
    /// every length the blocked AVX2 sum splits differently (including
    /// fewer rounds than one block), with random, all `-1` and zero
    /// challenges and seeds.
    fn check<F: CoefficientProducts>() {
        let mut rng = XorShiftRng::from_seed([0x5c; 16]);
        let mut expanded = Vec::new();
        for k in 1..=6 {
            let u: Vec<F> = (0..k).map(|_| F::random(&mut rng)).collect();
            let init = F::random(&mut rng);
            expand_coefficient_products(&u, init, &mut expanded);
            assert_eq!(expanded, naive(&u, init), "k = {k}");
        }

        assert!(F::sum_coefficient_products(&[]).is_empty());
        for k in [1usize, 2, 3, 4, 5, 6, 7, 8, 9, 11] {
            for proofs in [1usize, 2, 3, 65] {
                let products: Vec<(Vec<F>, F)> = (0..proofs)
                    .map(|p| match p % 5 {
                        1 => (alloc::vec![-F::ONE; k], -F::ONE),
                        3 => {
                            let mut u: Vec<F> = (0..k).map(|_| F::random(&mut rng)).collect();
                            u[p % k] = F::ZERO;
                            (u, F::random(&mut rng))
                        }
                        _ => (
                            (0..k).map(|_| F::random(&mut rng)).collect(),
                            F::random(&mut rng),
                        ),
                    })
                    .collect();
                let mut expected = alloc::vec![F::ZERO; 1 << k];
                for (u, init) in &products {
                    for (e, c) in expected.iter_mut().zip(naive(u, *init)) {
                        *e += c;
                    }
                }
                assert_eq!(sum_coefficient_products_scalar(&products), expected);
                assert_eq!(
                    F::sum_coefficient_products(&products),
                    expected,
                    "k = {k}, {proofs} proofs"
                );
            }
        }
    }

    #[test]
    fn coefficient_product_sums_match_naive() {
        check::<Fp>();
        check::<Fq>();
    }
}
