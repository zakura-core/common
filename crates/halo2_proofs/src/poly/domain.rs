//! Contains utilities for performing polynomial arithmetic over an evaluation
//! domain that is of a suitable size for the application.

use crate::{
    arithmetic::{best_fft, parallelize},
    multicore,
    plonk::Assigned,
};

use super::{Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation};

use ff::WithSmallOrderMulGroup;
use group::ff::{BatchInvert, Field};

use std::{any::Any, fmt, marker::PhantomData, sync::Arc};

#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;

/// The current Orchard circuit's last queried row is six rows behind the
/// challenge point.
const ORCHARD_LAST_ROTATION: i32 = -6;

type PolynomialTransformBatch<F> = (
    Vec<Polynomial<F, Coeff>>,
    Vec<Polynomial<F, ExtendedLagrangeCoeff>>,
);

/// FFT twiddles retained by a proving key.
///
/// The table lengths bind these twiddles to an [`EvaluationDomain`]'s base and
/// extended sizes. For a fixed field, those sizes uniquely determine the roots
/// of unity used to build the tables. Each cached transform asserts those
/// lengths before use so a cache cannot silently be used with another domain.
/// The fields are private so caches can only be built by
/// [`EvaluationDomain::proving_key_twiddles`] or cloned from one it built.
///
/// Clones share all retained allocations. This matters because [`ProvingKey`] is
/// cloneable and these tables are intended to be retained, not rebuilt.
/// Exact equivalence with the uncached transforms across the supported domain
/// shapes is covered by
/// `test_batched_lagrange_transforms_match_independent_transforms`.
///
/// [`ProvingKey`]: crate::plonk::ProvingKey
#[derive(Clone)]
pub(crate) struct ProvingKeyTwiddles<F> {
    base_inverse: Arc<[F]>,
    extended_forward: Arc<[F]>,
    base_inverse_tables: Arc<[Vec<F>]>,
    extended_forward_tables: Arc<[Vec<F>]>,
}

impl<F> fmt::Debug for ProvingKeyTwiddles<F> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProvingKeyTwiddles")
            .field("base_inverse_len", &self.base_inverse.len())
            .field("extended_forward_len", &self.extended_forward.len())
            .finish()
    }
}

/// This structure contains precomputed constants and other details needed for
/// performing operations on an evaluation domain of size $2^k$ and an extended
/// domain of size $2^{k} * j$ with $j \neq 0$.
#[derive(Clone, Debug)]
pub struct EvaluationDomain<F: Field> {
    n: u64,
    k: u32,
    extended_k: u32,
    omega: F,
    omega_inv: F,
    orchard_last_omega: F,
    extended_omega: F,
    extended_omega_inv: F,
    g_coset: F,
    g_coset_inv: F,
    quotient_poly_degree: u64,
    ifft_divisor: F,
    extended_ifft_divisor: F,
    sparse_vanishing_divisor: F,
    t_evaluations: Vec<F>,
    barycentric_weight: F,
}

impl<F: WithSmallOrderMulGroup<3>> EvaluationDomain<F> {
    /// This constructs a new evaluation domain object based on the provided
    /// values $j, k$.
    pub fn new(j: u32, k: u32) -> Self {
        // quotient_poly_degree * params.n - 1 is the degree of the quotient polynomial
        let quotient_poly_degree = (j - 1) as u64;

        // n = 2^k
        let n = 1u64 << k;

        // We need to work within an extended domain, not params.k but params.k + i
        // for some integer i such that 2^(params.k + i) is sufficiently large to
        // describe the quotient polynomial.
        let mut extended_k = k;
        while (1 << extended_k) < (n * quotient_poly_degree) {
            extended_k += 1;
        }

        // ensure extended_k <= S
        assert!(extended_k <= F::S);

        let mut extended_omega = F::ROOT_OF_UNITY;

        // Get extended_omega, the 2^{extended_k}'th root of unity
        // The loop computes extended_omega = omega^{2 ^ (S - extended_k)}
        // Notice that extended_omega ^ {2 ^ extended_k} = omega ^ {2^S} = 1.
        for _ in extended_k..F::S {
            extended_omega = extended_omega.square();
        }
        let extended_omega = extended_omega;
        let mut extended_omega_inv = extended_omega; // Inversion computed later

        // Get omega, the 2^{k}'th root of unity (i.e. n'th root of unity)
        // The loop computes omega = extended_omega ^ {2 ^ (extended_k - k)}
        //           = (omega^{2 ^ (S - extended_k)})  ^ {2 ^ (extended_k - k)}
        //           = omega ^ {2 ^ (S - k)}.
        // Notice that omega ^ {2^k} = omega ^ {2^S} = 1.
        let mut omega = extended_omega;
        for _ in k..extended_k {
            omega = omega.square();
        }
        let omega = omega;
        let mut omega_inv = omega; // Inversion computed later

        // We use zeta here because we know it generates a coset, and it's available
        // already.
        // The coset evaluation domain is:
        // zeta {1, extended_omega, extended_omega^2, ..., extended_omega^{(2^extended_k) - 1}}
        let g_coset = F::ZETA;
        let g_coset_inv = g_coset.square();

        let mut t_evaluations = Vec::with_capacity(1 << (extended_k - k));
        {
            // Compute the evaluations of t(X) = X^n - 1 in the coset evaluation domain.
            // We don't have to compute all of them, because it will repeat.
            let orig = F::ZETA.pow_vartime([n]);
            let step = extended_omega.pow_vartime([n]);
            let mut cur = orig;
            loop {
                t_evaluations.push(cur);
                cur *= &step;
                if cur == orig {
                    break;
                }
            }
            assert_eq!(t_evaluations.len(), 1 << (extended_k - k));

            // Subtract 1 from each to give us t_evaluations[i] = t(zeta * extended_omega^i)
            for coeff in &mut t_evaluations {
                *coeff -= &F::ONE;
            }

            // Invert, because we're dividing by this polynomial.
            // We invert in a batch, below.
        }

        let mut ifft_divisor = F::from(1 << k); // Inversion computed later
        let mut extended_ifft_divisor = F::from(1 << extended_k); // Inversion computed later

        // In coefficient form, division by X^n - 1 over the extended coset
        // requires division by g^N - 1, where N is the extended domain size.
        let mut sparse_vanishing_divisor = g_coset.pow_vartime([1u64 << extended_k]);
        sparse_vanishing_divisor -= F::ONE;
        debug_assert!(!bool::from(sparse_vanishing_divisor.is_zero()));

        // The barycentric weight of 1 over the evaluation domain
        // 1 / \prod_{i != 0} (1 - omega^i)
        let mut barycentric_weight = F::from(n); // Inversion computed later

        // Compute batch inversion
        t_evaluations
            .iter_mut()
            .chain(Some(&mut ifft_divisor))
            .chain(Some(&mut extended_ifft_divisor))
            .chain(Some(&mut sparse_vanishing_divisor))
            .chain(Some(&mut barycentric_weight))
            .chain(Some(&mut extended_omega_inv))
            .chain(Some(&mut omega_inv))
            .batch_invert();

        let orchard_last_omega =
            omega_inv.pow_vartime([u64::from(ORCHARD_LAST_ROTATION.unsigned_abs())]);

        EvaluationDomain {
            n,
            k,
            extended_k,
            omega,
            omega_inv,
            orchard_last_omega,
            extended_omega,
            extended_omega_inv,
            g_coset,
            g_coset_inv,
            quotient_poly_degree,
            ifft_divisor,
            extended_ifft_divisor,
            sparse_vanishing_divisor,
            t_evaluations,
            barycentric_weight,
        }
    }

    /// Obtains a polynomial in Lagrange form when given a vector of Lagrange
    /// coefficients of size `n`; panics if the provided vector is the wrong
    /// length.
    pub fn lagrange_from_vec(&self, values: Vec<F>) -> Polynomial<F, LagrangeCoeff> {
        assert_eq!(values.len(), self.n as usize);

        Polynomial {
            values,
            _marker: PhantomData,
        }
    }

    /// Obtains a polynomial in coefficient form when given a vector of
    /// coefficients of size `n`; panics if the provided vector is the wrong
    /// length.
    pub fn coeff_from_vec(&self, values: Vec<F>) -> Polynomial<F, Coeff> {
        assert_eq!(values.len(), self.n as usize);

        Polynomial {
            values,
            _marker: PhantomData,
        }
    }

    /// Returns an empty (zero) polynomial in the coefficient basis
    pub fn empty_coeff(&self) -> Polynomial<F, Coeff> {
        Polynomial {
            values: vec![F::ZERO; self.n as usize],
            _marker: PhantomData,
        }
    }

    /// Returns an empty (zero) polynomial in the Lagrange coefficient basis
    pub fn empty_lagrange(&self) -> Polynomial<F, LagrangeCoeff> {
        Polynomial {
            values: vec![F::ZERO; self.n as usize],
            _marker: PhantomData,
        }
    }

    /// Returns an empty (zero) polynomial in the Lagrange coefficient basis, with
    /// deferred inversions.
    pub(crate) fn empty_lagrange_assigned(&self) -> Polynomial<Assigned<F>, LagrangeCoeff> {
        Polynomial {
            values: vec![F::ZERO.into(); self.n as usize],
            _marker: PhantomData,
        }
    }

    /// Returns a constant polynomial in the Lagrange coefficient basis
    pub fn constant_lagrange(&self, scalar: F) -> Polynomial<F, LagrangeCoeff> {
        Polynomial {
            values: vec![scalar; self.n as usize],
            _marker: PhantomData,
        }
    }

    /// Returns an empty (zero) polynomial in the extended Lagrange coefficient
    /// basis
    pub fn empty_extended(&self) -> Polynomial<F, ExtendedLagrangeCoeff> {
        Polynomial {
            values: vec![F::ZERO; self.extended_len()],
            _marker: PhantomData,
        }
    }

    /// Returns a constant polynomial in the extended Lagrange coefficient
    /// basis
    pub fn constant_extended(&self, scalar: F) -> Polynomial<F, ExtendedLagrangeCoeff> {
        Polynomial {
            values: vec![scalar; self.extended_len()],
            _marker: PhantomData,
        }
    }

    /// This takes us from an n-length vector into the coefficient form.
    ///
    /// This function will panic if the provided vector is not the correct
    /// length.
    pub fn lagrange_to_coeff(&self, mut a: Polynomial<F, LagrangeCoeff>) -> Polynomial<F, Coeff> {
        assert_eq!(a.values.len(), 1 << self.k);

        // Perform inverse FFT to obtain the polynomial in coefficient form
        Self::ifft(&mut a.values, self.omega_inv, self.k, self.ifft_divisor);

        Polynomial {
            values: a.values,
            _marker: PhantomData,
        }
    }

    /// This takes us from an n-length coefficient vector into a coset of the extended
    /// evaluation domain, rotating by `rotation` if desired.
    pub fn coeff_to_extended(
        &self,
        mut a: Polynomial<F, Coeff>,
    ) -> Polynomial<F, ExtendedLagrangeCoeff> {
        assert_eq!(a.values.len(), 1 << self.k);

        self.distribute_powers_zeta(&mut a.values, true);
        Self::fft_zero_padded(&mut a.values, self.extended_omega, self.k, self.extended_k);

        Polynomial {
            values: a.values,
            _marker: PhantomData,
        }
    }

    /// Builds the FFT twiddles retained by a proving key.
    pub(crate) fn proving_key_twiddles(&self) -> ProvingKeyTwiddles<F> {
        let base_inverse = twiddle_table(self.omega_inv, 1 << self.k);
        let extended_forward = twiddle_table(self.extended_omega, self.extended_len());
        let base_inverse_tables = butterfly_twiddle_tables(&base_inverse, 1 << self.k);
        let extended_forward_tables =
            butterfly_twiddle_tables(&extended_forward, self.extended_len());
        ProvingKeyTwiddles {
            base_inverse: Arc::from(base_inverse),
            extended_forward: Arc::from(extended_forward),
            base_inverse_tables: Arc::from(base_inverse_tables),
            extended_forward_tables: Arc::from(extended_forward_tables),
        }
    }

    /// Converts a Lagrange polynomial to coefficient form using proving-key
    /// twiddles.
    pub(crate) fn lagrange_to_coeff_with_twiddles(
        &self,
        mut polynomial: Polynomial<F, LagrangeCoeff>,
        twiddles: &ProvingKeyTwiddles<F>,
    ) -> Polynomial<F, Coeff> {
        assert_eq!(polynomial.len(), 1 << self.k);
        assert_eq!(twiddles.base_inverse.len(), (1 << self.k) / 2);

        bitreverse_permute(&mut polynomial.values, self.k);
        field_butterfly_after_prefix(
            &mut polynomial.values,
            1,
            1,
            &twiddles.base_inverse,
            &twiddles.base_inverse_tables,
            0,
            parallel_depth(),
        );
        normalize_inverse_fft(&mut polynomial.values, self.k, self.ifft_divisor, true);

        Polynomial {
            values: polynomial.values,
            _marker: PhantomData,
        }
    }

    /// Converts a coefficient polynomial to extended-coset form using
    /// proving-key twiddles.
    pub(crate) fn coeff_to_extended_with_twiddles(
        &self,
        mut polynomial: Polynomial<F, Coeff>,
        twiddles: &ProvingKeyTwiddles<F>,
    ) -> Polynomial<F, ExtendedLagrangeCoeff> {
        assert_eq!(polynomial.len(), 1 << self.k);
        assert_eq!(twiddles.extended_forward.len(), self.extended_len() / 2);

        self.distribute_powers_zeta(&mut polynomial.values, true);
        Self::fft_zero_padded_with_twiddles(
            &mut polynomial.values,
            self.k,
            self.extended_k,
            &twiddles.extended_forward,
            &twiddles.extended_forward_tables,
            parallel_depth(),
        );

        Polynomial {
            values: polynomial.values,
            _marker: PhantomData,
        }
    }

    /// Converts several Lagrange polynomials to coefficient and
    /// extended-coset form, parallelizing across polynomials.
    ///
    /// Every polynomial must have this domain's base length, which is not
    /// encoded in [`Polynomial`]'s basis marker. The shared twiddle tables are
    /// derived from this domain, remain immutable, and are dropped when the
    /// batch completes. Each job owns its coefficient buffers, and collecting
    /// the indexed parallel iterator preserves input order.
    ///
    /// Exact equivalence with the independent transforms, including base and
    /// extended domains of size one and explicit one- and three-thread pools,
    /// is covered by
    /// `test_batched_lagrange_transforms_match_independent_transforms`.
    pub(crate) fn batch_lagrange_to_coeff_and_extended(
        &self,
        polynomials: &[Polynomial<F, LagrangeCoeff>],
        twiddles: &ProvingKeyTwiddles<F>,
    ) -> PolynomialTransformBatch<F> {
        if polynomials.is_empty() {
            return (Vec::new(), Vec::new());
        }

        assert_eq!(twiddles.base_inverse.len(), (1 << self.k) / 2);
        assert_eq!(twiddles.extended_forward.len(), self.extended_len() / 2);

        // Rayon below schedules one complete pair of transforms per
        // polynomial. The keygen and prover call sites expose fixed,
        // permutation, or advice polynomials as coarse-grained jobs, so both
        // FFTs disable nested Rayon joins and leave work stealing at the
        // polynomial boundary. A depth of zero changes only scheduling: the
        // butterflies retain their recursive, depth-first traversal for cache
        // locality.
        const INNER_PARALLEL_DEPTH: u32 = 0;

        let transform = |polynomial: &Polynomial<F, LagrangeCoeff>| {
            assert_eq!(polynomial.len(), 1 << self.k);

            let mut values = polynomial.values.clone();
            bitreverse_permute(&mut values, self.k);
            field_butterfly_after_prefix(
                &mut values,
                1,
                1,
                &twiddles.base_inverse,
                &twiddles.base_inverse_tables,
                0,
                INNER_PARALLEL_DEPTH,
            );
            normalize_inverse_fft(&mut values, self.k, self.ifft_divisor, false);
            let polynomial = Polynomial {
                values,
                _marker: PhantomData,
            };

            let mut extended = polynomial.clone();
            self.distribute_powers_zeta_serial(&mut extended.values, true);
            Self::fft_zero_padded_with_twiddles(
                &mut extended.values,
                self.k,
                self.extended_k,
                &twiddles.extended_forward,
                &twiddles.extended_forward_tables,
                INNER_PARALLEL_DEPTH,
            );
            let extended = Polynomial {
                values: extended.values,
                _marker: PhantomData,
            };
            (polynomial, extended)
        };

        #[cfg(feature = "multicore")]
        let transformed = polynomials.par_iter().map(transform).collect::<Vec<_>>();
        #[cfg(not(feature = "multicore"))]
        let transformed = polynomials.iter().map(transform).collect::<Vec<_>>();

        transformed.into_iter().unzip()
    }

    /// Rotate the extended domain polynomial over the original domain.
    pub fn rotate_extended(
        &self,
        poly: &Polynomial<F, ExtendedLagrangeCoeff>,
        rotation: Rotation,
    ) -> Polynomial<F, ExtendedLagrangeCoeff> {
        let new_rotation = ((1 << (self.extended_k - self.k)) * rotation.0.abs()) as usize;

        let mut poly = poly.clone();

        if rotation.0 >= 0 {
            poly.values.rotate_left(new_rotation);
        } else {
            poly.values.rotate_right(new_rotation);
        }

        poly
    }

    /// This takes us from the extended evaluation domain and gets us the
    /// quotient polynomial coefficients.
    ///
    /// This function will panic if the provided vector is not the correct
    /// length.
    // TODO/FIXME: caller should be responsible for truncating
    pub fn extended_to_coeff(&self, mut a: Polynomial<F, ExtendedLagrangeCoeff>) -> Vec<F> {
        assert_eq!(a.values.len(), self.extended_len());

        // Inverse FFT
        Self::ifft(
            &mut a.values,
            self.extended_omega_inv,
            self.extended_k,
            self.extended_ifft_divisor,
        );

        // Distribute powers to move from coset; opposite from the
        // transformation we performed earlier.
        self.distribute_powers_zeta(&mut a.values, false);

        // Truncate it to match the size of the quotient polynomial; the
        // evaluation domain might be slightly larger than necessary because
        // it always lies on a power-of-two boundary.
        a.values
            .truncate((&self.n * self.quotient_poly_degree) as usize);

        a.values
    }

    /// Converts a quotient numerator from the extended evaluation domain into
    /// the coefficient-form quotient pieces.
    ///
    /// If the extended domain has size `N = m * n`, its coset coefficient ring
    /// is `F[X] / (X^N - c)` for `c = g^N`. In that ring,
    ///
    /// ```text
    /// (X^n - 1)^-1 = (1 + X^n + ... + X^((m - 1)n)) / (c - 1).
    /// ```
    ///
    /// Applying this sparse inverse blockwise replaces `N` pointwise field
    /// multiplications with `n` fixed-constant multiplications and block
    /// additions. The output permutation, inverse-FFT normalization, sparse
    /// division, and construction of quotient pieces are fused so the full
    /// coefficient buffer is not reversed, normalized, divided, and copied in
    /// separate passes. Independent coefficient columns are processed in
    /// parallel. This is equivalent for arbitrary numerator evaluations, not
    /// only for numerators that are polynomially divisible by `X^n - 1`.
    pub(crate) fn quotient_numerator_to_pieces_with_twiddles(
        &self,
        mut polynomial: Polynomial<F, ExtendedLagrangeCoeff>,
        twiddles: &ProvingKeyTwiddles<F>,
    ) -> Vec<Polynomial<F, Coeff>> {
        assert_eq!(polynomial.len(), self.extended_len());
        assert_eq!(twiddles.extended_forward.len(), self.extended_len() / 2);

        if self.quotient_poly_degree == 0 {
            return Vec::new();
        }

        bitreverse_permute(&mut polynomial.values, self.extended_k);
        field_butterfly_after_prefix(
            &mut polynomial.values,
            1,
            1,
            &twiddles.extended_forward,
            &twiddles.extended_forward_tables,
            0,
            parallel_depth(),
        );

        let block_len = self.n as usize;
        let block_count = self.extended_len() / block_len;
        let piece_count = self.quotient_poly_degree as usize;
        assert!(piece_count <= block_count);

        let mut piece_values = (0..piece_count)
            .map(|_| vec![F::ZERO; block_len])
            .collect::<Vec<_>>();
        write_quotient_columns(
            &polynomial.values,
            &mut piece_values,
            block_len,
            block_count,
            [
                self.extended_ifft_divisor,
                self.extended_ifft_divisor * self.g_coset_inv,
                self.extended_ifft_divisor * self.g_coset,
            ],
            self.sparse_vanishing_divisor,
            self.extended_k,
            parallel_depth(),
        );

        piece_values
            .into_iter()
            .map(|values| Polynomial {
                values,
                _marker: PhantomData,
            })
            .collect()
    }

    /// Converts an extended-domain polynomial to untruncated coefficient form
    /// using the proving key's forward twiddles.
    ///
    /// An inverse DFT is a forward DFT with every nonzero output index
    /// reversed, followed by the usual scaling. This avoids retaining a
    /// separate extended-inverse table. Exact equivalence with
    /// [`EvaluationDomain::extended_to_coeff`] is covered by
    /// `test_batched_lagrange_transforms_match_independent_transforms`,
    /// including explicit one- and three-thread pools.
    #[cfg(test)]
    fn extended_to_coeff_full_with_twiddles(
        &self,
        mut polynomial: Polynomial<F, ExtendedLagrangeCoeff>,
        twiddles: &ProvingKeyTwiddles<F>,
    ) -> Vec<F> {
        assert_eq!(polynomial.len(), self.extended_len());
        assert_eq!(twiddles.extended_forward.len(), self.extended_len() / 2);

        bitreverse_permute(&mut polynomial.values, self.extended_k);
        field_butterfly_after_prefix(
            &mut polynomial.values,
            1,
            1,
            &twiddles.extended_forward,
            &twiddles.extended_forward_tables,
            0,
            parallel_depth(),
        );
        polynomial.values[1..].reverse();

        // Combine inverse-FFT normalization with removal of the coset twist,
        // so each coefficient requires exactly one field multiplication.
        let scales = [
            self.extended_ifft_divisor,
            self.extended_ifft_divisor * self.g_coset_inv,
            self.extended_ifft_divisor * self.g_coset,
        ];
        parallelize(&mut polynomial.values, |values, mut index| {
            for value in values {
                *value *= &scales[index % scales.len()];
                index += 1;
            }
        });
        polynomial.values
    }

    /// This divides the polynomial (in the extended domain) by the vanishing
    /// polynomial of the $2^k$ size domain.
    pub fn divide_by_vanishing_poly(
        &self,
        mut a: Polynomial<F, ExtendedLagrangeCoeff>,
    ) -> Polynomial<F, ExtendedLagrangeCoeff> {
        assert_eq!(a.values.len(), self.extended_len());

        // Divide to obtain the quotient polynomial in the coset evaluation
        // domain.
        parallelize(&mut a.values, |h, mut index| {
            for h in h {
                *h *= &self.t_evaluations[index % self.t_evaluations.len()];
                index += 1;
            }
        });

        Polynomial {
            values: a.values,
            _marker: PhantomData,
        }
    }

    /// Given a slice of group elements `[a_0, a_1, a_2, ...]`, this returns
    /// `[a_0, [zeta]a_1, [zeta^2]a_2, a_3, [zeta]a_4, [zeta^2]a_5, a_6, ...]`,
    /// where zeta is a cube root of unity in the multiplicative subgroup with
    /// order (p - 1), i.e. zeta^3 = 1.
    ///
    /// `into_coset` should be set to `true` when moving into the coset,
    /// and `false` when moving out. This toggles the choice of `zeta`.
    fn distribute_powers_zeta(&self, a: &mut [F], into_coset: bool) {
        let coset_powers = if into_coset {
            [self.g_coset, self.g_coset_inv]
        } else {
            [self.g_coset_inv, self.g_coset]
        };
        parallelize(a, |a, mut index| {
            for a in a {
                // Distribute powers to move into/from coset
                let i = index % (coset_powers.len() + 1);
                if i != 0 {
                    *a *= &coset_powers[i - 1];
                }
                index += 1;
            }
        });
    }

    fn distribute_powers_zeta_serial(&self, values: &mut [F], into_coset: bool) {
        let coset_powers = if into_coset {
            [self.g_coset, self.g_coset_inv]
        } else {
            [self.g_coset_inv, self.g_coset]
        };
        for (index, value) in values.iter_mut().enumerate() {
            let power = index % (coset_powers.len() + 1);
            if power != 0 {
                *value *= &coset_powers[power - 1];
            }
        }
    }

    fn ifft(a: &mut [F], omega_inv: F, log_n: u32, divisor: F) {
        best_fft(a, omega_inv, log_n);
        parallelize(a, |a, _| {
            for a in a {
                // Finish iFFT
                *a *= &divisor;
            }
        });
    }

    fn fft_zero_padded(coefficients: &mut Vec<F>, omega: F, log_n: u32, extended_log_n: u32) {
        assert!(log_n <= extended_log_n);

        let n = 1 << log_n;
        let extended_n = 1 << extended_log_n;
        let extension = extended_n / n;

        assert_eq!(coefficients.len(), n);
        if extension == 1 {
            best_fft(coefficients, omega, log_n);
            return;
        }
        if n == 1 {
            coefficients.resize(extended_n, coefficients[0]);
            return;
        }

        let twiddles = twiddle_table(omega, extended_n);
        let tables = butterfly_twiddle_tables(&twiddles, extended_n);
        Self::fft_zero_padded_with_twiddles(
            coefficients,
            log_n,
            extended_log_n,
            &twiddles,
            &tables,
            parallel_depth(),
        );
    }

    fn fft_zero_padded_with_twiddles(
        coefficients: &mut Vec<F>,
        log_n: u32,
        extended_log_n: u32,
        twiddles: &[F],
        tables: &[Vec<F>],
        parallel_depth: u32,
    ) {
        assert!(log_n <= extended_log_n);

        let n = 1 << log_n;
        let extended_n = 1 << extended_log_n;
        let extension = extended_n / n;

        assert_eq!(coefficients.len(), n);
        assert_eq!(twiddles.len(), extended_n / 2);

        // A constant polynomial needs no butterfly arithmetic.
        if n == 1 {
            coefficients.resize(extended_n, coefficients[0]);
            return;
        }

        // For an n-length input, bitreverse_extended(i) is
        // extension * bitreverse_n(i). The omitted radix-2 stages would copy
        // each live coefficient across an `extension`-sized chunk. Materialize
        // the first retained stage directly instead of writing and rereading
        // those replicated chunks. Thus no butterfly multiplication has an
        // implicit zero operand, and only log_n stages remain: O(N log n)
        // arithmetic for extended-domain size N and coefficient count n.
        let mut values = Vec::with_capacity(extended_n);
        let mut right_values = vec![F::ZERO; extension];
        // `arithmetic::recursive_butterfly_arithmetic` uses twiddle stride
        // N / L at a node of length L. The first retained node has
        // L = 2 * extension, so its stride is N / (2 * extension) = n / 2.
        let first_twiddle_chunk = n / 2;
        for pair in 0..n / 2 {
            let left = coefficients[bitreverse(2 * pair, log_n)];
            let right = coefficients[bitreverse(2 * pair + 1, log_n)];

            let mut left_value = left;
            left_value += &right;
            values.push(left_value);
            right_values[0] = left;
            right_values[0] -= &right;

            for (index, right_value) in right_values.iter_mut().enumerate().skip(1) {
                let mut t = right;
                t *= &twiddles[index * first_twiddle_chunk];

                let mut left_value = left;
                left_value += &t;
                values.push(left_value);

                *right_value = left;
                *right_value -= &t;
            }
            values.extend_from_slice(&right_values);
        }
        debug_assert_eq!(values.len(), extended_n);

        // Each 2 * extension chunk contains the first retained stage. Continue
        // with the other log_n - 1 butterfly stages. A zero parallel depth
        // still traverses recursively to retain cache locality.
        field_butterfly_after_prefix(
            &mut values,
            2 * extension,
            1,
            twiddles,
            tables,
            0,
            parallel_depth,
        );
        *coefficients = values;
    }

    /// Get the size of the extended domain
    pub fn extended_len(&self) -> usize {
        1 << self.extended_k
    }

    /// Get $\omega$, the generator of the $2^k$ order multiplicative subgroup.
    pub fn get_omega(&self) -> F {
        self.omega
    }

    /// Get $\omega^{-1}$, the inverse of the generator of the $2^k$ order
    /// multiplicative subgroup.
    pub fn get_omega_inv(&self) -> F {
        self.omega_inv
    }

    /// Get the generator of the extended domain's multiplicative subgroup.
    pub fn get_extended_omega(&self) -> F {
        self.extended_omega
    }

    /// Multiplies a value by some power of $\omega$, essentially rotating over
    /// the domain.
    pub fn rotate_omega(&self, value: F, rotation: Rotation) -> F {
        match rotation.0 {
            0 => value,
            1 => value * self.get_omega(),
            -1 => value * self.get_omega_inv(),
            ORCHARD_LAST_ROTATION => value * self.orchard_last_omega,
            rotation if rotation > 0 => {
                value
                    * self
                        .get_omega()
                        .pow_vartime([u64::from(rotation.unsigned_abs())])
            }
            rotation => {
                value
                    * self
                        .get_omega_inv()
                        .pow_vartime([u64::from(rotation.unsigned_abs())])
            }
        }
    }

    /// Computes evaluations (at the point `x`, where `xn = x^n`) of Lagrange
    /// basis polynomials `l_i(X)` defined such that `l_i(omega^i) = 1` and
    /// `l_i(omega^j) = 0` for all `j != i` at each provided rotation `i`.
    ///
    /// # Implementation
    ///
    /// The polynomial
    ///     $$\prod_{j=0,j \neq i}^{n - 1} (X - \omega^j)$$
    /// has a root at all points in the domain except $\omega^i$, where it evaluates to
    ///     $$\prod_{j=0,j \neq i}^{n - 1} (\omega^i - \omega^j)$$
    /// and so we divide that polynomial by this value to obtain $l_i(X)$. Since
    ///     $$\prod_{j=0,j \neq i}^{n - 1} (X - \omega^j)
    ///       = \frac{X^n - 1}{X - \omega^i}$$
    /// then $l_i(x)$ for some $x$ is evaluated as
    ///     $$\left(\frac{x^n - 1}{x - \omega^i}\right)
    ///       \cdot \left(\frac{1}{\prod_{j=0,j \neq i}^{n - 1} (\omega^i - \omega^j)}\right).$$
    /// We refer to
    ///     $$1 \over \prod_{j=0,j \neq i}^{n - 1} (\omega^i - \omega^j)$$
    /// as the barycentric weight of $\omega^i$.
    ///
    /// We know that for $i = 0$
    ///     $$\frac{1}{\prod_{j=0,j \neq i}^{n - 1} (\omega^i - \omega^j)} = \frac{1}{n}.$$
    ///
    /// If we multiply $(1 / n)$ by $\omega^i$ then we obtain
    ///     $$\frac{1}{\prod_{j=0,j \neq 0}^{n - 1} (\omega^i - \omega^j)}
    ///       = \frac{1}{\prod_{j=0,j \neq i}^{n - 1} (\omega^i - \omega^j)}$$
    /// which is the barycentric weight of $\omega^i$.
    pub fn l_i_range<I: IntoIterator<Item = i32> + Clone>(
        &self,
        x: F,
        xn: F,
        rotations: I,
    ) -> Vec<F> {
        let mut results;
        {
            let rotations = rotations.clone().into_iter();
            results = Vec::with_capacity(rotations.size_hint().1.unwrap_or(0));
            for rotation in rotations {
                let rotation = Rotation(rotation);
                let result = x - self.rotate_omega(F::ONE, rotation);
                results.push(result);
            }
            results.iter_mut().batch_invert();
        }

        let common = (xn - F::ONE) * self.barycentric_weight;
        for (rotation, result) in rotations.into_iter().zip(results.iter_mut()) {
            let rotation = Rotation(rotation);
            *result = self.rotate_omega(*result * common, rotation);
        }

        results
    }

    /// Gets the quotient polynomial's degree (as a multiple of n)
    pub fn get_quotient_poly_degree(&self) -> usize {
        self.quotient_poly_degree as usize
    }

    /// Obtain a pinned version of this evaluation domain; a structure with the
    /// minimal parameters needed to determine the rest of the evaluation
    /// domain.
    pub fn pinned(&self) -> PinnedEvaluationDomain<'_, F> {
        PinnedEvaluationDomain {
            k: &self.k,
            extended_k: &self.extended_k,
            omega: &self.omega,
        }
    }
}

fn twiddle_table<F: Field>(omega: F, n: usize) -> Vec<F> {
    let mut twiddles = Vec::with_capacity(n / 2);
    let mut twiddle = F::ONE;
    for index in 0..n / 2 {
        twiddles.push(twiddle);
        if index + 1 < n / 2 {
            twiddle *= &omega;
        }
    }
    twiddles
}

fn parallel_depth() -> u32 {
    let mut depth = 0;
    let mut tasks = 1;
    let threads = multicore::current_num_threads();
    while tasks < threads {
        depth += 1;
        tasks <<= 1;
    }
    depth
}

fn bitreverse_permute<F>(values: &mut [F], log_n: u32) {
    for index in 0..values.len() {
        let reversed = bitreverse(index, log_n);
        if index < reversed {
            values.swap(index, reversed);
        }
    }
}

fn normalize_inverse_fft<F: Field>(values: &mut Vec<F>, exponent: u32, divisor: F, parallel: bool) {
    // Pasta exposes a partial Montgomery reduction for this exact scaling.
    // Downcast the allocation once so the element loop has no type checks.
    if let Some(values) = (values as &mut dyn Any).downcast_mut::<Vec<crate::pasta::Fp>>() {
        normalize_inverse_fft_pasta(
            values,
            exponent,
            parallel,
            crate::arithmetic::mul_fp_by_inverse_power_of_two,
        );
        return;
    }
    if let Some(values) = (values as &mut dyn Any).downcast_mut::<Vec<crate::pasta::Fq>>() {
        normalize_inverse_fft_pasta(
            values,
            exponent,
            parallel,
            crate::arithmetic::mul_fq_by_inverse_power_of_two,
        );
        return;
    }

    let scale = |values: &mut [F], _| {
        for value in values {
            *value *= &divisor;
        }
    };
    if parallel {
        parallelize(values, scale);
    } else {
        scale(values, 0);
    }
}

fn normalize_inverse_fft_pasta<F, M>(values: &mut [F], exponent: u32, parallel: bool, multiply: M)
where
    F: Field,
    M: Fn(&F, u32) -> F + Copy + Send + Sync,
{
    let scale = |values: &mut [F], _| {
        for value in values {
            *value = multiply(value, exponent);
        }
    };
    if parallel {
        parallelize(values, scale);
    } else {
        scale(values, 0);
    }
}

fn bitreverse(value: usize, bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        value.reverse_bits() >> (usize::BITS - bits)
    }
}

/// Node half-lengths at or below this size use the strided scalar combine
/// loop; larger nodes use a contiguous per-level twiddle table.
const CACHED_TWIDDLE_MIN_HALF: usize = 32;

/// Builds contiguous per-level twiddle tables for the butterfly combine step.
fn butterfly_twiddle_tables<F: Field>(twiddles: &[F], len: usize) -> Vec<Vec<F>> {
    let mut tables = Vec::new();
    let mut half = len / 2;
    let mut chunk = 1;
    while half > CACHED_TWIDDLE_MIN_HALF {
        tables.push((1..half).map(|index| twiddles[index * chunk]).collect());
        half /= 2;
        chunk *= 2;
    }
    tables
}

fn field_butterfly_after_prefix<F: Field>(
    values: &mut Vec<F>,
    completed_chunk_len: usize,
    twiddle_chunk: usize,
    twiddles: &[F],
    tables: &[Vec<F>],
    level: usize,
    parallel_depth: u32,
) {
    // Polynomial batches already supply outer parallelism. Preserve the
    // ordinary parallel transform for standalone FFTs.
    if parallel_depth == 0 {
        if let Some(values) = (values as &mut dyn Any).downcast_mut::<Vec<crate::pasta::Fp>>() {
            crate::pasta::arithmetic::fft_fp_after_prefix(
                values,
                completed_chunk_len,
                twiddle_chunk,
                |index| downcast_field(twiddles[index]),
            );
            return;
        }
        if let Some(values) = (values as &mut dyn Any).downcast_mut::<Vec<crate::pasta::Fq>>() {
            crate::pasta::arithmetic::fft_fq_after_prefix(
                values,
                completed_chunk_len,
                twiddle_chunk,
                |index| downcast_field(twiddles[index]),
            );
            return;
        }
    }
    recursive_butterfly_after_prefix(
        values,
        completed_chunk_len,
        twiddle_chunk,
        twiddles,
        tables,
        level,
        parallel_depth,
    );
}

fn recursive_butterfly_after_prefix<F: Field>(
    values: &mut [F],
    completed_chunk_len: usize,
    twiddle_chunk: usize,
    twiddles: &[F],
    tables: &[Vec<F>],
    level: usize,
    parallel_depth: u32,
) {
    let len = values.len();
    if len == completed_chunk_len {
        return;
    }

    let (left, right) = values.split_at_mut(len / 2);
    if len / 2 > completed_chunk_len {
        if parallel_depth > 0 {
            multicore::join(
                || {
                    recursive_butterfly_after_prefix(
                        left,
                        completed_chunk_len,
                        twiddle_chunk * 2,
                        twiddles,
                        tables,
                        level + 1,
                        parallel_depth - 1,
                    )
                },
                || {
                    recursive_butterfly_after_prefix(
                        right,
                        completed_chunk_len,
                        twiddle_chunk * 2,
                        twiddles,
                        tables,
                        level + 1,
                        parallel_depth - 1,
                    )
                },
            );
        } else {
            recursive_butterfly_pair_after_prefix(
                left,
                right,
                completed_chunk_len,
                twiddle_chunk * 2,
                twiddles,
                tables,
                level + 1,
            );
        }
    }

    butterfly_chunk(left, right, twiddle_chunk, twiddles, tables, level);
}

/// Recursively processes two equal-sized field FFT chunks together. The FFT
/// sizes are powers of two, so every recursive level contains an exact pair.
/// Keeping the two independent twiddle multiplications adjacent gives the CPU
/// two dependency chains to schedule.
fn recursive_butterfly_pair_after_prefix<F: Field>(
    first: &mut [F],
    second: &mut [F],
    completed_chunk_len: usize,
    twiddle_chunk: usize,
    twiddles: &[F],
    tables: &[Vec<F>],
    level: usize,
) {
    debug_assert_eq!(first.len(), second.len());
    let len = first.len();
    debug_assert!(len.is_power_of_two());
    debug_assert!(completed_chunk_len.is_power_of_two());
    debug_assert!(completed_chunk_len <= len);
    if len == completed_chunk_len {
        return;
    }

    let (first_left, first_right) = first.split_at_mut(len / 2);
    let (second_left, second_right) = second.split_at_mut(len / 2);
    if len / 2 > completed_chunk_len {
        recursive_butterfly_pair_after_prefix(
            first_left,
            first_right,
            completed_chunk_len,
            twiddle_chunk * 2,
            twiddles,
            tables,
            level + 1,
        );
        recursive_butterfly_pair_after_prefix(
            second_left,
            second_right,
            completed_chunk_len,
            twiddle_chunk * 2,
            twiddles,
            tables,
            level + 1,
        );
    }

    butterfly_chunk_pair(
        first_left,
        first_right,
        second_left,
        second_right,
        twiddle_chunk,
        twiddles,
        tables,
        level,
    );
}

#[inline(always)]
fn butterfly_chunk<F: Field>(
    left: &mut [F],
    right: &mut [F],
    twiddle_chunk: usize,
    twiddles: &[F],
    tables: &[Vec<F>],
    level: usize,
) {
    // Handle the unity twiddle without a field multiplication.
    let (first_left, left) = left.split_at_mut(1);
    let (first_right, right) = right.split_at_mut(1);
    let t = first_right[0];
    first_right[0] = first_left[0];
    first_left[0] += &t;
    first_right[0] -= &t;

    if let Some(table) = tables.get(level) {
        debug_assert_eq!(table.len(), right.len());
        for (right, twiddle) in right.iter_mut().zip(table) {
            *right *= twiddle;
        }
        for (left, right) in left.iter_mut().zip(right.iter_mut()) {
            let t = *right;
            *right = *left;
            *left += &t;
            *right -= &t;
        }
    } else {
        for (index, (left, right)) in left.iter_mut().zip(right.iter_mut()).enumerate() {
            let mut t = *right;
            t *= &twiddles[(index + 1) * twiddle_chunk];
            *right = *left;
            *left += &t;
            *right -= &t;
        }
    }
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn butterfly_chunk_pair<F: Field>(
    first_left: &mut [F],
    first_right: &mut [F],
    second_left: &mut [F],
    second_right: &mut [F],
    twiddle_chunk: usize,
    twiddles: &[F],
    tables: &[Vec<F>],
    level: usize,
) {
    debug_assert_eq!(first_left.len(), first_right.len());
    debug_assert_eq!(first_left.len(), second_left.len());
    debug_assert_eq!(first_left.len(), second_right.len());

    // Handle both unity twiddles without field multiplications.
    let (first_a, first_left) = first_left.split_at_mut(1);
    let (first_b, first_right) = first_right.split_at_mut(1);
    let (second_a, second_left) = second_left.split_at_mut(1);
    let (second_b, second_right) = second_right.split_at_mut(1);
    let first_t = first_b[0];
    let second_t = second_b[0];
    first_b[0] = first_a[0];
    second_b[0] = second_a[0];
    first_a[0] += &first_t;
    second_a[0] += &second_t;
    first_b[0] -= &first_t;
    second_b[0] -= &second_t;

    if let Some(table) = tables.get(level) {
        debug_assert_eq!(table.len(), first_right.len());
        for (right, twiddle) in first_right.iter_mut().zip(table) {
            *right *= twiddle;
        }
        for (right, twiddle) in second_right.iter_mut().zip(table) {
            *right *= twiddle;
        }
        for ((first_left, first_right), (second_left, second_right)) in first_left
            .iter_mut()
            .zip(first_right.iter_mut())
            .zip(second_left.iter_mut().zip(second_right.iter_mut()))
        {
            let first_t = *first_right;
            let second_t = *second_right;
            *first_right = *first_left;
            *second_right = *second_left;
            *first_left += &first_t;
            *second_left += &second_t;
            *first_right -= &first_t;
            *second_right -= &second_t;
        }
        return;
    }

    for (index, ((first_left, first_right), (second_left, second_right))) in first_left
        .iter_mut()
        .zip(first_right.iter_mut())
        .zip(second_left.iter_mut().zip(second_right.iter_mut()))
        .enumerate()
    {
        let twiddle = &twiddles[(index + 1) * twiddle_chunk];
        let mut first_t = *first_right;
        let mut second_t = *second_right;
        first_t *= twiddle;
        second_t *= twiddle;

        *first_right = *first_left;
        *second_right = *second_left;
        *first_left += &first_t;
        *second_left += &second_t;
        *first_right -= &first_t;
        *second_right -= &second_t;
    }
}

fn write_quotient_columns<F: Field>(
    transform: &Vec<F>,
    piece_values: &mut Vec<Vec<F>>,
    block_len: usize,
    block_count: usize,
    scales: [F; 3],
    sparse_vanishing_divisor: F,
    exponent: u32,
    parallel_depth: u32,
) {
    if let Some(transform) = (transform as &dyn Any).downcast_ref::<Vec<crate::pasta::Fp>>() {
        let piece_values = (piece_values as &mut dyn Any)
            .downcast_mut::<Vec<Vec<crate::pasta::Fp>>>()
            .expect("the quotient pieces and transform have the same field");
        let scales: [crate::pasta::Fp; 3] = scales.map(downcast_field);
        write_quotient_columns_inner(
            transform,
            piece_values,
            block_len,
            block_count,
            downcast_field(sparse_vanishing_divisor),
            parallel_depth,
            |value, index| match index % scales.len() {
                0 => crate::arithmetic::mul_fp_by_inverse_power_of_two(&value, exponent),
                power => value * scales[power],
            },
        );
        return;
    }
    if let Some(transform) = (transform as &dyn Any).downcast_ref::<Vec<crate::pasta::Fq>>() {
        let piece_values = (piece_values as &mut dyn Any)
            .downcast_mut::<Vec<Vec<crate::pasta::Fq>>>()
            .expect("the quotient pieces and transform have the same field");
        let scales: [crate::pasta::Fq; 3] = scales.map(downcast_field);
        write_quotient_columns_inner(
            transform,
            piece_values,
            block_len,
            block_count,
            downcast_field(sparse_vanishing_divisor),
            parallel_depth,
            |value, index| match index % scales.len() {
                0 => crate::arithmetic::mul_fq_by_inverse_power_of_two(&value, exponent),
                power => value * scales[power],
            },
        );
        return;
    }

    write_quotient_columns_inner(
        transform,
        piece_values,
        block_len,
        block_count,
        sparse_vanishing_divisor,
        parallel_depth,
        |value, index| value * scales[index % scales.len()],
    );
}

fn write_quotient_columns_inner<F, S>(
    transform: &[F],
    piece_values: &mut [Vec<F>],
    block_len: usize,
    block_count: usize,
    sparse_vanishing_divisor: F,
    parallel_depth: u32,
    scale: S,
) where
    F: Field,
    S: Fn(F, usize) -> F + Copy + Send + Sync,
{
    let output_blocks = piece_values
        .iter_mut()
        .map(Vec::as_mut_slice)
        .collect::<Vec<_>>();
    let quotient_columns = QuotientColumnContext {
        transform,
        block_len,
        block_count,
        sparse_vanishing_divisor,
    };
    quotient_columns.write(output_blocks, 0, parallel_depth, scale);
}

fn downcast_field<F: Field, T: Field>(value: F) -> T {
    *(&value as &dyn Any)
        .downcast_ref::<T>()
        .expect("the polynomial and domain fields have the same type")
}

struct QuotientColumnContext<'a, F> {
    transform: &'a [F],
    block_len: usize,
    block_count: usize,
    sparse_vanishing_divisor: F,
}

impl<F: Field> QuotientColumnContext<'_, F> {
    /// Converts aligned coefficient columns from a forward-transform result
    /// into quotient-piece columns. An inverse transform reads output zero
    /// unchanged and every other output in reverse order; indexing that
    /// permutation here avoids reversing the full transform buffer first.
    fn write<S>(
        &self,
        mut output_blocks: Vec<&mut [F]>,
        column_offset: usize,
        parallel_depth: u32,
        scale: S,
    ) where
        S: Fn(F, usize) -> F + Copy + Send + Sync,
    {
        debug_assert!(!output_blocks.is_empty());
        let column_len = output_blocks[0].len();
        debug_assert!(
            output_blocks
                .iter()
                .all(|output| output.len() == column_len)
        );
        debug_assert_eq!(self.transform.len(), self.block_len * self.block_count);

        if parallel_depth > 0 && column_len > 1 {
            let middle = column_len / 2;
            let mut left_outputs = Vec::with_capacity(output_blocks.len());
            let mut right_outputs = Vec::with_capacity(output_blocks.len());
            for output in output_blocks {
                let (left, right) = output.split_at_mut(middle);
                left_outputs.push(left);
                right_outputs.push(right);
            }

            multicore::join(
                || self.write(left_outputs, column_offset, parallel_depth - 1, scale),
                || {
                    self.write(
                        right_outputs,
                        column_offset + middle,
                        parallel_depth - 1,
                        scale,
                    )
                },
            );
            return;
        }

        let transform_len = self.transform.len();
        let piece_count = output_blocks.len();
        let mut numerators = vec![F::ZERO; self.block_count];
        let mut local_column = 0;
        while local_column < column_len {
            let column = column_offset + local_column;
            let mut numerator_sum = F::ZERO;
            for (block, numerator) in numerators.iter_mut().enumerate() {
                let coefficient_index = block * self.block_len + column;
                let transform_index = if coefficient_index == 0 {
                    0
                } else {
                    transform_len - coefficient_index
                };
                *numerator = scale(self.transform[transform_index], coefficient_index);
                numerator_sum += &*numerator;
            }

            let mut h_next = numerator_sum * self.sparse_vanishing_divisor;
            if self.block_count - 1 < piece_count {
                output_blocks[self.block_count - 1][local_column] = h_next;
            }
            for block in (1..self.block_count).rev() {
                let h_previous = numerators[block] + h_next;
                if block - 1 < piece_count {
                    output_blocks[block - 1][local_column] = h_previous;
                }
                h_next = h_previous;
            }
            local_column += 1;
        }
    }
}

/// Represents the minimal parameters that determine an `EvaluationDomain`.
#[allow(dead_code)]
#[derive(Debug)]
pub struct PinnedEvaluationDomain<'a, F: Field> {
    k: &'a u32,
    extended_k: &'a u32,
    omega: &'a F,
}

#[test]
fn lazy_fft_matches_canonical_stages_on_both_fields() {
    use rand::{SeedableRng, rngs::StdRng};

    fn check<F: WithSmallOrderMulGroup<3>>() {
        let mut rng = StdRng::seed_from_u64(0x4646_542d_4c41_5a59);
        for k in 0..=11 {
            let domain = EvaluationDomain::<F>::new(3, k);
            let twiddles = twiddle_table(domain.omega, 1 << k);
            let input: Vec<_> = (0..1 << k)
                .map(|i| match i % 5 {
                    0 => F::ZERO,
                    1 => F::ONE,
                    2 => -F::ONE,
                    _ => F::random(&mut rng),
                })
                .collect();
            for completed in [1, 2, 4, 16] {
                if completed > input.len() {
                    continue;
                }
                let mut expected = input.clone();
                recursive_butterfly_after_prefix(&mut expected, completed, 1, &twiddles, &[], 0, 0);
                let mut actual = input.clone();
                field_butterfly_after_prefix(&mut actual, completed, 1, &twiddles, &[], 0, 0);
                assert_eq!(actual, expected, "k={k}, completed={completed}");
            }
        }
    }
    check::<crate::pasta::Fp>();
    check::<crate::pasta::Fq>();
}

#[test]
fn test_zero_padded_fft_matches_best_fft() {
    use crate::{arithmetic::best_fft, pasta::pallas::Scalar};

    for k in 0..=8 {
        for extension_log in 0..=4 {
            let degree = if extension_log == 0 {
                2
            } else {
                (1 << extension_log) + 1
            };
            let domain = EvaluationDomain::<Scalar>::new(degree, k);
            assert_eq!(domain.extended_k, k + extension_log);

            let coefficients = (1..=(1u64 << k)).map(Scalar::from).collect::<Vec<_>>();
            let mut expected = coefficients.clone();
            domain.distribute_powers_zeta(&mut expected, true);
            expected.resize(domain.extended_len(), Scalar::ZERO);
            best_fft(&mut expected, domain.extended_omega, domain.extended_k);

            let coefficients = domain.coeff_from_vec(coefficients);
            let actual = domain.coeff_to_extended(coefficients);

            assert_eq!(&actual[..], &expected);
        }
    }
}

#[test]
fn test_batched_lagrange_transforms_match_independent_transforms() {
    use crate::pasta::pallas::Scalar;

    for k in 0..=8 {
        for extension_log in 0..=4 {
            let degree = if extension_log == 0 {
                2
            } else {
                (1 << extension_log) + 1
            };
            let domain = EvaluationDomain::<Scalar>::new(degree, k);
            let twiddles = domain.proving_key_twiddles();
            let polynomials = (0..5)
                .map(|polynomial| {
                    let values = (0..1usize << k)
                        .map(|coefficient| {
                            Scalar::from(((polynomial + 1) * (coefficient + 2)) as u64)
                        })
                        .collect();
                    domain.lagrange_from_vec(values)
                })
                .collect::<Vec<_>>();

            let check = || {
                let expected_coefficients = polynomials
                    .iter()
                    .cloned()
                    .map(|polynomial| domain.lagrange_to_coeff(polynomial))
                    .collect::<Vec<_>>();
                let expected_extended = expected_coefficients
                    .iter()
                    .cloned()
                    .map(|polynomial| domain.coeff_to_extended(polynomial))
                    .collect::<Vec<_>>();
                let (coefficients, extended) =
                    domain.batch_lagrange_to_coeff_and_extended(&polynomials, &twiddles);

                assert_eq!(coefficients.len(), expected_coefficients.len());
                assert_eq!(extended.len(), expected_extended.len());
                for ((polynomial, actual), expected) in polynomials
                    .iter()
                    .zip(&coefficients)
                    .zip(&expected_coefficients)
                {
                    assert_eq!(&actual[..], &expected[..]);
                    let cached =
                        domain.lagrange_to_coeff_with_twiddles(polynomial.clone(), &twiddles);
                    assert_eq!(&cached[..], &expected[..]);
                }
                for ((coefficient, actual), expected) in expected_coefficients
                    .iter()
                    .zip(&extended)
                    .zip(&expected_extended)
                {
                    assert_eq!(&actual[..], &expected[..]);
                    let cached =
                        domain.coeff_to_extended_with_twiddles(coefficient.clone(), &twiddles);
                    assert_eq!(&cached[..], &expected[..]);

                    let expected_back = domain.extended_to_coeff(expected.clone());
                    let mut cached_coefficients =
                        domain.extended_to_coeff_full_with_twiddles(expected.clone(), &twiddles);
                    cached_coefficients.truncate(expected_back.len());
                    assert_eq!(cached_coefficients, expected_back);
                }

                // Quotient construction applies the inverse transform to
                // arbitrary extended-domain evaluations, not only evaluations
                // produced by the zero-padded forward transform above.
                let mut arbitrary_extended = domain.empty_extended();
                for (index, value) in arbitrary_extended.iter_mut().enumerate() {
                    *value = Scalar::from((index + 1) as u64);
                }
                let expected = domain.extended_to_coeff(arbitrary_extended.clone());
                let mut actual =
                    domain.extended_to_coeff_full_with_twiddles(arbitrary_extended, &twiddles);
                actual.truncate(expected.len());
                assert_eq!(actual, expected);
            };

            #[cfg(feature = "multicore")]
            for threads in [1, 3] {
                maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(threads)
                    .build()
                    .unwrap()
                    .install(check);
            }
            #[cfg(not(feature = "multicore"))]
            check();
        }
    }

    let domain = EvaluationDomain::<Scalar>::new(9, 3);
    let twiddles = domain.proving_key_twiddles();
    let (coefficients, extended) = domain.batch_lagrange_to_coeff_and_extended(&[], &twiddles);
    assert!(coefficients.is_empty());
    assert!(extended.is_empty());
}

#[test]
fn test_cached_base_inverse_transform_for_both_pasta_fields() {
    use crate::pasta::{Fp, Fq};

    fn check<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        let domain = EvaluationDomain::<F>::new(9, 4);
        let twiddles = domain.proving_key_twiddles();
        let lagrange = domain.lagrange_from_vec((1..=1 << 4).map(F::from).collect());
        let expected = domain.lagrange_to_coeff(lagrange.clone());
        let actual = domain.lagrange_to_coeff_with_twiddles(lagrange, &twiddles);
        assert_eq!(&actual[..], &expected[..]);
    }

    check::<Fp>();
    check::<Fq>();
}

#[test]
fn test_sparse_quotient_division_matches_pointwise_division() {
    use crate::pasta::pallas::Scalar;

    let check = || {
        // Cover the empty quotient, every extended-domain ratio through
        // Orchard's, a ratio-one domain, a non-power-of-two quotient degree
        // that is truncated after division, and the next larger ratio.
        for &(max_degree, k) in &[(1, 3), (2, 0), (3, 3), (4, 3), (6, 4), (9, 11), (10, 4)] {
            let domain = EvaluationDomain::<Scalar>::new(max_degree, k);
            let twiddles = domain.proving_key_twiddles();
            let mut numerator = domain.empty_extended();
            for (index, value) in numerator.iter_mut().enumerate() {
                *value = Scalar::from(((index as u64) + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15));
            }

            // The existing path is an independent reference: pointwise
            // division in the evaluation domain followed by the uncached
            // inverse transform and its separate coset untwist.
            let expected =
                domain.extended_to_coeff(domain.divide_by_vanishing_poly(numerator.clone()));
            let actual = domain
                .quotient_numerator_to_pieces_with_twiddles(numerator, &twiddles)
                .into_iter()
                .flat_map(|piece| piece.values)
                .collect::<Vec<_>>();
            assert_eq!(actual, expected);
        }
    };

    #[cfg(feature = "multicore")]
    for threads in [1, 3] {
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(check);
    }
    #[cfg(not(feature = "multicore"))]
    check();
}

#[test]
fn test_sparse_quotient_division_matches_pointwise_on_basis_vectors() {
    use crate::pasta::{pallas, vesta};

    fn check<F: WithSmallOrderMulGroup<3>>() {
        // Both division paths are linear in the numerator. Equality on every
        // standard basis vector therefore covers every possible numerator for
        // these small domains, without relying on a single dense fixture.
        for &(max_degree, k) in &[
            (1, 3),
            (2, 0),
            (2, 3),
            (3, 3),
            (4, 3),
            (5, 3),
            (6, 3),
            (9, 3),
            (10, 3),
        ] {
            let domain = EvaluationDomain::<F>::new(max_degree, k);
            let twiddles = domain.proving_key_twiddles();

            for basis_index in 0..domain.extended_len() {
                let mut numerator = domain.empty_extended();
                numerator[basis_index] = F::ONE;

                let expected =
                    domain.extended_to_coeff(domain.divide_by_vanishing_poly(numerator.clone()));
                let actual = domain
                    .quotient_numerator_to_pieces_with_twiddles(numerator, &twiddles)
                    .into_iter()
                    .flat_map(|piece| piece.values)
                    .collect::<Vec<_>>();
                assert_eq!(
                    actual, expected,
                    "max_degree={max_degree}, k={k}, basis_index={basis_index}"
                );
            }
        }
    }

    check::<pallas::Scalar>();
    check::<vesta::Scalar>();
}

#[test]
fn test_orchard_proving_key_twiddle_cache_size_and_sharing() {
    use crate::pasta::pallas::Scalar;

    const ORCHARD_DEGREE: u32 = 9;
    const ORCHARD_K: u32 = 11;
    const EXPECTED_FLAT_PAYLOAD_BYTES: usize = 288 * 1024;
    const EXPECTED_LEVEL_PAYLOAD_BYTES: usize = 585_312;
    #[cfg(target_pointer_width = "64")]
    const EXPECTED_LEVEL_RETAINED_BYTES: usize = 585_656;

    let domain = EvaluationDomain::<Scalar>::new(ORCHARD_DEGREE, ORCHARD_K);
    let twiddles = domain.proving_key_twiddles();
    assert_eq!(std::mem::size_of::<Scalar>(), 32);
    assert_eq!(twiddles.base_inverse.len(), 1 << (ORCHARD_K - 1));
    assert_eq!(
        twiddles.extended_forward.len(),
        1 << (domain.extended_k - 1)
    );
    assert_eq!(
        (twiddles.base_inverse.len() + twiddles.extended_forward.len())
            * std::mem::size_of::<Scalar>(),
        EXPECTED_FLAT_PAYLOAD_BYTES
    );

    let level_tables = twiddles
        .base_inverse_tables
        .iter()
        .chain(twiddles.extended_forward_tables.iter())
        .collect::<Vec<_>>();
    assert!(
        level_tables
            .iter()
            .all(|table| table.len() == table.capacity())
    );
    let level_payload_bytes =
        level_tables.iter().map(|table| table.len()).sum::<usize>() * std::mem::size_of::<Scalar>();
    assert_eq!(level_payload_bytes, EXPECTED_LEVEL_PAYLOAD_BYTES);

    // This stable accounting excludes allocator metadata and the two `Arc`
    // reference-count headers, whose sizes are implementation details.
    #[cfg(target_pointer_width = "64")]
    assert_eq!(
        level_payload_bytes
            + level_tables.len() * std::mem::size_of::<Vec<Scalar>>()
            + 2 * std::mem::size_of::<Arc<[Vec<Scalar>]>>(),
        EXPECTED_LEVEL_RETAINED_BYTES
    );

    let cloned = twiddles.clone();
    assert!(Arc::ptr_eq(&twiddles.base_inverse, &cloned.base_inverse));
    assert!(Arc::ptr_eq(
        &twiddles.extended_forward,
        &cloned.extended_forward
    ));
    assert!(Arc::ptr_eq(
        &twiddles.base_inverse_tables,
        &cloned.base_inverse_tables
    ));
    assert!(Arc::ptr_eq(
        &twiddles.extended_forward_tables,
        &cloned.extended_forward_tables
    ));
}

#[test]
fn test_rotate() {
    use rand::rng;

    use crate::arithmetic::eval_polynomial;
    use crate::pasta::pallas::Scalar;

    let domain = EvaluationDomain::<Scalar>::new(1, 3);
    let mut rng = rng();

    let mut poly = domain.empty_lagrange();
    assert_eq!(poly.len(), 8);
    for value in poly.iter_mut() {
        *value = Scalar::random(&mut rng);
    }

    let poly_rotated_cur = poly.rotate(Rotation::cur());
    let poly_rotated_next = poly.rotate(Rotation::next());
    let poly_rotated_prev = poly.rotate(Rotation::prev());

    let poly = domain.lagrange_to_coeff(poly);
    let poly_rotated_cur = domain.lagrange_to_coeff(poly_rotated_cur);
    let poly_rotated_next = domain.lagrange_to_coeff(poly_rotated_next);
    let poly_rotated_prev = domain.lagrange_to_coeff(poly_rotated_prev);

    let x = Scalar::random(&mut rng);

    assert_eq!(
        eval_polynomial(&poly[..], x),
        eval_polynomial(&poly_rotated_cur[..], x)
    );
    assert_eq!(
        eval_polynomial(&poly[..], x * domain.omega),
        eval_polynomial(&poly_rotated_next[..], x)
    );
    assert_eq!(
        eval_polynomial(&poly[..], x * domain.omega_inv),
        eval_polynomial(&poly_rotated_prev[..], x)
    );
}

#[test]
fn test_rotate_omega_fast_paths_match_exponentiation() {
    use crate::pasta::pallas::Scalar;

    let domain = EvaluationDomain::<Scalar>::new(1, 11);
    let value = Scalar::from(42);

    for rotation in [
        Rotation::cur(),
        Rotation::next(),
        Rotation::prev(),
        Rotation(ORCHARD_LAST_ROTATION),
        Rotation(2),
        Rotation(-2),
        Rotation(7),
        Rotation(-7),
    ] {
        let exponent = u64::from(rotation.0.unsigned_abs());
        let expected = if rotation.0 >= 0 {
            value * domain.get_omega().pow_vartime([exponent])
        } else {
            value * domain.get_omega_inv().pow_vartime([exponent])
        };
        assert_eq!(domain.rotate_omega(value, rotation), expected);
    }
}

#[test]
fn test_l_i() {
    use rand::rng;

    use crate::arithmetic::{eval_polynomial, lagrange_interpolate};
    use crate::pasta::pallas::Scalar;
    let domain = EvaluationDomain::<Scalar>::new(1, 3);

    let mut l = vec![];
    let mut points = vec![];
    for i in 0..8 {
        points.push(domain.omega.pow([i, 0, 0, 0]));
    }
    for i in 0..8 {
        let mut l_i = vec![Scalar::zero(); 8];
        l_i[i] = Scalar::ONE;
        let l_i = lagrange_interpolate(&points[..], &l_i[..]);
        l.push(l_i);
    }

    let x = Scalar::random(&mut rng());
    let xn = x.pow([8, 0, 0, 0]);

    let evaluations = domain.l_i_range(x, xn, -7..=7);
    for i in 0..8 {
        assert_eq!(eval_polynomial(&l[i][..], x), evaluations[7 + i]);
        assert_eq!(eval_polynomial(&l[(8 - i) % 8][..], x), evaluations[7 - i]);
    }
}

#[test]
fn test_copy_rotated_chunk_extended() {
    use pasta_curves::pallas;
    use rand::rng;

    let k = 11;
    let domain = EvaluationDomain::<pallas::Base>::new(3, k);

    // Create a random polynomial.
    let mut poly = domain.empty_extended();
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
        for (chunk_index, chunk) in domain
            .rotate_extended(&poly, rotation)
            .chunks(chunk_size)
            .enumerate()
        {
            let mut actual = vec![pallas::Base::ZERO; chunk.len()];
            let rotation_abs = (rotation.0.unsigned_abs() as usize)
                * domain.get_quotient_poly_degree().next_power_of_two();
            poly.copy_rotated_chunk_helper(
                rotation.0 < 0,
                rotation_abs,
                chunk_size,
                chunk_index,
                &mut actual,
            );
            assert_eq!(actual, chunk);
        }
    }
}
