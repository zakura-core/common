//! This module contains an implementation of the polynomial commitment scheme
//! described in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//!
//! # Sparse IPA masking polynomial
//!
//! The hiding transformation used by [`create_proof`] comes from
//! `PC_DL.Open` in Appendix A.2 of [BCMS20]. Before the inner-product
//! argument (IPA), the prover commits to a random polynomial $s(X)$ such that
//! $s(x) = 0$, receives a nonzero challenge $\xi$, and folds
//!
//! $$p'(X) = p(X) - p(x) + \xi s(X).$$
//!
//! BCMS20 samples $s$ across the entire supported degree range. Only a short
//! prefix is needed for honest-verifier zero knowledge, however. The argument
//! is as follows.
//!
//! Let $n = 2^k$, and let $u_0, \ldots, u_{k-1}$ be the nonzero IPA folding
//! challenges in their transcript order. After all folds, the prover reveals
//!
//! $$c = \langle p', \lambda \rangle,$$
//!
//! where, writing $i = \sum_t i_t 2^t$ in binary,
//!
//! $$\lambda_i = \prod_{t=0}^{k-1} u_{k-1-t}^{-i_t}.$$
//!
//! Sample $s_1, \ldots, s_{m-1}$ uniformly, set
//! $s_0 = -\sum_{i=1}^{m-1} s_i x^i$, and set all coefficients from $m$
//! onward to zero. This samples $s$ uniformly from
//!
//! $$V_m = \{s \in \mathbb F^m :
//! \langle s,(1,x,\ldots,x^{m-1})\rangle=0\}.$$
//!
//! The scalar $c$ is uniform unless the linear functional $\lambda$ vanishes
//! on $V_m$. The annihilator of $V_m$ is spanned by
//! $(1,x,\ldots,x^{m-1})$. Since $\lambda_0 = 1$, the exceptional case is
//! therefore exactly
//!
//! $$\lambda_i = x^i \quad\text{for every }0 \leq i < m.$$
//!
//! For each power of two $2^t < m$, this equality requires the independent
//! challenge equation $u_{k-1-t}^{-1} = x^{2^t}$. These equations are also
//! sufficient, by the product formula for $\lambda_i$. Thus, for independent
//! uniform challenges in $\mathbb F^*$, the exceptional probability is
//!
//! $$(|\mathbb F|-1)^{-\lceil\log_2 m\rceil}.$$
//!
//! All group messages before $c$ are independently Pedersen-blinded. Outside
//! the exceptional event, the usual honest-verifier simulator samples $c$ and
//! the final combined blind uniformly, samples all but one group message, and
//! solves the verifier equation for the remaining message using $\xi^{-1}$.
//! This gives the honest transcript distribution. The same random-oracle
//! programming argument as BCMS20 Appendix A.3.1 applies after Fiat-Shamir.
//!
//! In particular, an MSM with twelve polynomial coefficients and one
//! commitment blind has thirteen scalar coefficients. Here $m=12$, so four
//! independent challenge equations would all need to hold. For either Pasta
//! scalar field, whose order is greater than $2^{254}$, this probability is
//! below $2^{-1016}$. The implementation deliberately pads the mask to degree
//! 64 ($m=65$, plus the commitment blind), requiring seven equations and
//! lowering the bound below $2^{-1778}$. If $n \leq 65$ it instead samples the
//! full available polynomial; then the exceptional functional is the public
//! evaluation functional and reveals nothing.
//!
//! This argument uses the standard nonzero challenge space from BCMS20. The
//! implementation already requires every $u_j$ to be nonzero in order to
//! invert it. If a transcript encoding samples the whole field, including its
//! negligible zero event adds its existing $O(k/|\mathbb F|)$ abort probability
//! and the event $\xi=0$ adds at most $1/|\mathbb F|$ to the privacy distance.
//!
//! [BCMS20]: https://eprint.iacr.org/2020/499

use super::{Coeff, LagrangeCoeff, Polynomial};
#[cfg(feature = "orbits")]
use crate::arithmetic::PreparedZeroCheck;
use crate::arithmetic::{best_fft, best_multiexp, parallelize, CurveAffine, CurveExt};
use crate::helpers::CurveRead;
#[cfg(feature = "batch")]
use crate::{InstanceWindowTable, INSTANCE_WINDOW_ENTRIES_PER_BASE, MAX_CACHED_INSTANCE_ROWS};

use ff::{Field, PrimeField};
use group::{Curve, Group};
use std::ops::{Add, AddAssign, Mul, MulAssign};
#[cfg(any(feature = "batch", feature = "orbits"))]
use std::{
    fmt,
    sync::{Arc, Mutex},
};

mod msm;
mod prover;
mod verifier;

pub use msm::MSM;
pub use prover::create_proof;
pub use verifier::{verify_proof, Accumulator, Guard};

use std::io;

/// These are the public parameters for the polynomial commitment scheme.
#[derive(Clone)]
#[cfg_attr(not(feature = "batch"), derive(Debug))]
pub struct Params<C: CurveAffine> {
    pub(crate) k: u32,
    pub(crate) n: u64,
    pub(crate) g: Vec<C>,
    pub(crate) g_lagrange: Vec<C>,
    pub(crate) w: C,
    pub(crate) u: C,
    #[cfg(feature = "batch")]
    instance_window_cache: InstanceWindowCache<C>,
    #[cfg(feature = "orbits")]
    zero_check_cache: ZeroCheckCache<C>,
    #[cfg(feature = "orbits")]
    lagrange_table_cache: ZeroCheckCache<C>,
}

/// A lazily built prepared fixed-base multiexp table — over `[g..., w, u]`
/// for [`Params::prepare_zero_checks`], or `[g_lagrange..., w, u]` for the
/// Lagrange half of [`Params::prepare_commitments`] — shared across clones
/// of the params that hold it. Never serialized; rebuilt on demand after
/// `read`.
#[cfg(feature = "orbits")]
#[derive(Clone)]
struct ZeroCheckCache<C: CurveAffine>(
    #[allow(clippy::type_complexity)] Arc<Mutex<Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>>>>,
);

#[cfg(feature = "orbits")]
impl<C: CurveAffine> Default for ZeroCheckCache<C> {
    fn default() -> Self {
        Self(Arc::new(Mutex::new(None)))
    }
}

#[cfg(feature = "orbits")]
impl<C: CurveAffine> fmt::Debug for ZeroCheckCache<C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let armed = self
            .0
            .lock()
            .map(|prepared| prepared.is_some())
            .unwrap_or(false);
        formatter
            .debug_tuple("ZeroCheckCache")
            .field(&armed)
            .finish()
    }
}

#[cfg(feature = "batch")]
#[derive(Clone)]
struct InstanceWindowCache<C>(Arc<Mutex<Option<Arc<Vec<C>>>>>);

#[cfg(feature = "batch")]
impl<C> Default for InstanceWindowCache<C> {
    fn default() -> Self {
        Self(Arc::new(Mutex::new(None)))
    }
}

#[cfg(feature = "batch")]
impl<C> InstanceWindowCache<C> {
    fn get_or_grow(&self, base_count: usize, initialize: impl FnOnce() -> Vec<C>) -> Arc<Vec<C>> {
        let required_len = base_count
            .checked_mul(INSTANCE_WINDOW_ENTRIES_PER_BASE)
            .expect("instance window table length fits in usize");
        let mut table = self
            .0
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(table) = table.as_ref().filter(|table| table.len() >= required_len) {
            return Arc::clone(table);
        }

        let initialized = Arc::new(initialize());
        assert_eq!(initialized.len(), required_len);
        *table = Some(Arc::clone(&initialized));
        initialized
    }
}

#[cfg(feature = "batch")]
impl<C: CurveAffine> fmt::Debug for Params<C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Params")
            .field("k", &self.k)
            .field("n", &self.n)
            .field("g", &self.g)
            .field("g_lagrange", &self.g_lagrange)
            .field("w", &self.w)
            .field("u", &self.u)
            .finish()
    }
}

#[cfg(feature = "batch")]
impl<C: CurveAffine> InstanceWindowTable<C> for Params<C> {
    fn instance_window_table(&self, base_count: usize) -> Arc<Vec<C>> {
        assert!(base_count <= MAX_CACHED_INSTANCE_ROWS);
        assert!(base_count <= self.g_lagrange.len());

        self.instance_window_cache.get_or_grow(base_count, || {
            let capacity = base_count
                .checked_mul(INSTANCE_WINDOW_ENTRIES_PER_BASE)
                .expect("instance window table length fits in usize");
            let mut projective = Vec::with_capacity(capacity);
            for base in &self.g_lagrange[..base_count] {
                let mut multiple = C::Curve::from(*base);
                for _ in 0..INSTANCE_WINDOW_ENTRIES_PER_BASE {
                    projective.push(multiple);
                    multiple += *base;
                }
            }

            let mut affine = vec![C::identity(); projective.len()];
            C::Curve::batch_normalize(&projective, &mut affine);
            affine
        })
    }
}

impl<C: CurveAffine> Params<C> {
    /// Initializes parameters for the curve, given a random oracle to draw
    /// points from.
    pub fn new(k: u32) -> Self {
        // This is usually a limitation on the curve, but we also want 32-bit
        // architectures to be supported.
        assert!(k < 32);

        // In src/arithmetic/fields.rs we ensure that usize is at least 32 bits.

        let n: u64 = 1 << k;

        let g_projective = {
            let mut g = Vec::with_capacity(n as usize);
            g.resize(n as usize, C::Curve::identity());

            parallelize(&mut g, move |g, start| {
                let hasher = C::CurveExt::hash_to_curve("Halo2-Parameters");

                for (i, g) in g.iter_mut().enumerate() {
                    let i = (i + start) as u32;

                    let mut message = [0u8; 5];
                    message[1..5].copy_from_slice(&i.to_le_bytes());

                    *g = hasher(&message);
                }
            });

            g
        };

        let g = {
            let mut g = vec![C::identity(); n as usize];
            parallelize(&mut g, |g, starts| {
                C::Curve::batch_normalize(&g_projective[starts..(starts + g.len())], g);
            });
            g
        };

        // Let's evaluate all of the Lagrange basis polynomials
        // using an inverse FFT.
        let mut alpha_inv = <<C as group::CurveAffine>::Curve as Group>::Scalar::ROOT_OF_UNITY_INV;
        for _ in k..C::Scalar::S {
            alpha_inv = alpha_inv.square();
        }
        let minv = C::Scalar::TWO_INV.pow_vartime([k as u64]);
        let mut g_lagrange_projective = g_projective;
        // Normalize the inverse FFT by scaling its inputs. The transform is
        // linear, and `g` is already affine, so each worker can share the
        // public scalar's precomputation across its generators.
        parallelize(&mut g_lagrange_projective, |output, start| {
            C::Curve::batch_mul_same_scalar_vartime(&g[start..start + output.len()], &minv, output);
        });

        let g_lagrange = {
            let mut g_lagrange = vec![C::identity(); n as usize];
            if !C::Curve::fft_vartime(&g_lagrange_projective, &mut g_lagrange, alpha_inv, k) {
                best_fft(&mut g_lagrange_projective, alpha_inv, k);
                parallelize(&mut g_lagrange, |g_lagrange, starts| {
                    C::Curve::batch_normalize(
                        &g_lagrange_projective[starts..(starts + g_lagrange.len())],
                        g_lagrange,
                    );
                });
            }
            drop(g_lagrange_projective);
            g_lagrange
        };

        let hasher = C::CurveExt::hash_to_curve("Halo2-Parameters");
        let w = hasher(&[1]).to_affine();
        let u = hasher(&[2]).to_affine();

        Params {
            k,
            n,
            g,
            g_lagrange,
            w,
            u,
            #[cfg(feature = "batch")]
            instance_window_cache: InstanceWindowCache::default(),
            #[cfg(feature = "orbits")]
            zero_check_cache: ZeroCheckCache::default(),
            #[cfg(feature = "orbits")]
            lagrange_table_cache: ZeroCheckCache::default(),
        }
    }

    /// This computes a commitment to a polynomial described by the provided
    /// slice of coefficients. The commitment will be blinded by the blinding
    /// factor `r`.
    pub fn commit(&self, poly: &Polynomial<C::Scalar, Coeff>, r: Blind<C::Scalar>) -> C::Curve {
        // A prepared table over [g..., w, u] (built by
        // `Params::prepare_commitments`, or shared from
        // `Params::prepare_zero_checks`) evaluates this commitment as a
        // fixed-base multiexp with the blind riding `w` and `u` unused.
        // Like `MSM::eval`, the routing is thread-gated: past
        // `PREPARED_MSM_MAX_THREADS` effective threads the planned
        // multiexp out-scales the prepared evaluation.
        #[cfg(feature = "orbits")]
        if crate::multicore::current_num_threads() <= msm::PREPARED_MSM_MAX_THREADS {
            if let Some(prepared) = self.zero_check() {
                let n = self.n as usize;
                if prepared.terms() == n + 2 && poly.len() == n {
                    let mut fixed = Vec::with_capacity(n + 2);
                    fixed.extend(poly.iter());
                    fixed.push(r.0);
                    fixed.push(C::Scalar::ZERO);
                    return prepared.multiexp_with_terms_vartime(&fixed, &[]);
                }
            }
        }

        let mut tmp_scalars = Vec::with_capacity(poly.len() + 1);
        let mut tmp_bases = Vec::with_capacity(poly.len() + 1);

        tmp_scalars.extend(poly.iter());
        tmp_scalars.push(r.0);

        tmp_bases.extend(self.g.iter());
        tmp_bases.push(self.w);

        best_multiexp::<C>(&tmp_scalars, &tmp_bases)
    }

    /// This commits to a polynomial using its evaluations over the $2^k$ size
    /// evaluation domain. The commitment will be blinded by the blinding factor
    /// `r`.
    pub fn commit_lagrange(
        &self,
        poly: &Polynomial<C::Scalar, LagrangeCoeff>,
        r: Blind<C::Scalar>,
    ) -> C::Curve {
        // The Lagrange-basis counterpart of `commit`'s prepared route,
        // over the [g_lagrange..., w, u] table built by
        // `Params::prepare_commitments`; same thread gate.
        #[cfg(feature = "orbits")]
        if crate::multicore::current_num_threads() <= msm::PREPARED_MSM_MAX_THREADS {
            if let Some(prepared) = self.lagrange_table() {
                let n = self.n as usize;
                if prepared.terms() == n + 2 && poly.len() == n {
                    let mut fixed = Vec::with_capacity(n + 2);
                    fixed.extend(poly.iter());
                    fixed.push(r.0);
                    fixed.push(C::Scalar::ZERO);
                    return prepared.multiexp_with_terms_vartime(&fixed, &[]);
                }
            }
        }

        let mut tmp_scalars = Vec::with_capacity(poly.len() + 1);
        let mut tmp_bases = Vec::with_capacity(poly.len() + 1);

        tmp_scalars.extend(poly.iter());
        tmp_scalars.push(r.0);

        tmp_bases.extend(self.g_lagrange.iter());
        tmp_bases.push(self.w);

        best_multiexp::<C>(&tmp_scalars, &tmp_bases)
    }

    /// Generates an empty multiscalar multiplication struct using the
    /// appropriate params.
    pub fn empty_msm(&self) -> MSM<'_, C> {
        MSM::new(self)
    }

    /// Getter for g generators
    pub fn get_g(&self) -> Vec<C> {
        self.g.clone()
    }

    /// Get the circuit size parameter k
    pub fn k(&self) -> u32 {
        self.k
    }

    /// Writes params to a buffer.
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.k.to_le_bytes())?;
        for g_element in &self.g {
            writer.write_all(g_element.to_bytes().as_ref())?;
        }
        for g_lagrange_element in &self.g_lagrange {
            writer.write_all(g_lagrange_element.to_bytes().as_ref())?;
        }
        writer.write_all(self.w.to_bytes().as_ref())?;
        writer.write_all(self.u.to_bytes().as_ref())?;

        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);

        let n: u64 = 1 << k;

        let g: Vec<_> = (0..n).map(|_| C::read(reader)).collect::<Result<_, _>>()?;
        let g_lagrange: Vec<_> = (0..n).map(|_| C::read(reader)).collect::<Result<_, _>>()?;

        let w = C::read(reader)?;
        let u = C::read(reader)?;

        Ok(Params {
            k,
            n,
            g,
            g_lagrange,
            w,
            u,
            #[cfg(feature = "batch")]
            instance_window_cache: InstanceWindowCache::default(),
            #[cfg(feature = "orbits")]
            zero_check_cache: ZeroCheckCache::default(),
            #[cfg(feature = "orbits")]
            lagrange_table_cache: ZeroCheckCache::default(),
        })
    }

    /// Builds and caches a prepared fixed-base zero-check over this SRS
    /// (the generators `g` plus `w` and `u`), which [`MSM::eval`] then
    /// routes its final identity test through — the proof-specific
    /// commitment terms ride along as the check's extra terms. On the
    /// Pasta curves this measured the verifier's final check ~1.5–2.4x
    /// faster; other curves without a prepared backend make this a no-op.
    ///
    /// The routing is thread-aware: on pools wider than
    /// `msm::PREPARED_MSM_MAX_THREADS` (currently eight) effective threads
    /// the unprepared planner out-scales the prepared evaluation (measured
    /// end-to-end on 16- and 32-thread pools), so `eval` falls back to the
    /// plain multiexp there and arming is never a pessimization — a
    /// wide-pool validator simply amortizes the preparation over the
    /// verifications that run on narrower pools.
    ///
    /// Preparation costs hundreds of milliseconds and tens of mebibytes
    /// at typical `k`, amortized across every subsequent verification
    /// with these params (batch verification folds many proofs into a
    /// single final check, so it also pays just one). The cache is shared
    /// with all clones of these params; it is never serialized, so call
    /// this again after [`Params::read`].
    ///
    /// Returns whether a prepared check was actually built and cached.
    /// `false` means arming was a no-op — the curve has no prepared
    /// backend, the backend declined (its prepared table for this SRS
    /// would exceed its internal memory budget; very large `k`), or the
    /// `orbits` feature (disabled by default) is off — and verification
    /// simply keeps evaluating the plain multiexp. Callers may ignore the
    /// result; long-lived validators that expect the speedup can assert
    /// or log it.
    pub fn prepare_zero_checks(&self) -> bool {
        #[cfg(feature = "orbits")]
        {
            let mut bases = Vec::with_capacity(self.g.len() + 2);
            bases.extend_from_slice(&self.g);
            bases.push(self.w);
            bases.push(self.u);
            if let Some(prepared) = C::CurveExt::try_prepare_zero_check(&bases) {
                *self
                    .zero_check_cache
                    .0
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(Arc::from(prepared));
                return true;
            }
        }
        false
    }

    /// The cached prepared zero-check, if [`Self::prepare_zero_checks`]
    /// built one.
    #[cfg(feature = "orbits")]
    pub(crate) fn zero_check(&self) -> Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>> {
        self.zero_check_cache
            .0
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }

    /// Builds and caches prepared fixed-base multiexp tables for the
    /// prover's commitments: the coefficient-basis table over `[g..., w, u]`
    /// (shared with [`Self::prepare_zero_checks`] — [`Self::commit`] and the
    /// verifier's final check use the same bases) and a second table over
    /// `[g_lagrange..., w, u]` for [`Self::commit_lagrange`]. When armed,
    /// both commit methods evaluate through the prepared tables on pools
    /// of at most `msm::PREPARED_MSM_MAX_THREADS` (currently eight)
    /// effective threads — measured 1.2–1.8x per commitment at 1–8 threads
    /// on x86-64 and Apple silicon alike, across full-width and
    /// witness-like (boolean, byte, zero-padded) coefficient
    /// distributions — and keep the planned multiexp on wider pools, where
    /// the prepared evaluation stops scaling, so arming is never a
    /// pessimization.
    ///
    /// Costs roughly twice [`Self::prepare_zero_checks`] (two tables, each
    /// hundreds of milliseconds and tens of mebibytes at typical `k`),
    /// amortized across every subsequent proof with these params; a table
    /// that is already armed is kept, so repeat calls are free. The caches
    /// are shared with all clones and never serialized; call again after
    /// [`Params::read`]. Returns whether both tables are armed (`false`
    /// when the `orbits` feature is off or the backend declined — a commit
    /// route without its table simply keeps the planned multiexp).
    pub fn prepare_commitments(&self) -> bool {
        #[cfg(feature = "orbits")]
        {
            // The tables depend only on the immutable bases, so a table
            // that is already armed is kept rather than rebuilt.
            if !(self.zero_check().is_some() || self.prepare_zero_checks()) {
                // Both tables have the same term count, so a coefficient
                // decline means the Lagrange build would decline too.
                return false;
            }
            if self.lagrange_table().is_some() {
                return true;
            }
            let mut bases = Vec::with_capacity(self.g_lagrange.len() + 2);
            bases.extend_from_slice(&self.g_lagrange);
            bases.push(self.w);
            bases.push(self.u);
            if let Some(prepared) = C::CurveExt::try_prepare_zero_check(&bases) {
                *self
                    .lagrange_table_cache
                    .0
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(Arc::from(prepared));
                return true;
            }
        }
        false
    }

    /// The cached Lagrange-basis prepared table, if
    /// [`Self::prepare_commitments`] built one.
    #[cfg(feature = "orbits")]
    pub(crate) fn lagrange_table(&self) -> Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>> {
        self.lagrange_table_cache
            .0
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }
}

#[cfg(test)]
const LAGRANGE_BASIS_HASH_LENGTH: usize = 32;

#[cfg(test)]
const EXPECTED_LAGRANGE_BASIS_HASHES: &[(u32, [u8; LAGRANGE_BASIS_HASH_LENGTH])] = &[
    (
        9,
        [
            0x6b, 0x3c, 0xb7, 0x0c, 0x4f, 0x39, 0x6e, 0x3e, 0xc3, 0x42, 0x06, 0x3e, 0x22, 0x02,
            0xa7, 0x74, 0xb6, 0x08, 0x1c, 0x9b, 0x87, 0xa1, 0xce, 0x1d, 0xbf, 0x45, 0x40, 0xdc,
            0x02, 0xab, 0xfa, 0x08,
        ],
    ),
    (
        10,
        [
            0x1f, 0x24, 0x05, 0xb6, 0x5b, 0xca, 0x87, 0xa7, 0x6a, 0xf8, 0xd0, 0x6d, 0x91, 0xa8,
            0x90, 0xd9, 0x5f, 0xaf, 0x3c, 0xdf, 0xd0, 0x49, 0x42, 0x58, 0xe0, 0xff, 0xff, 0x3c,
            0xac, 0xaa, 0xac, 0x38,
        ],
    ),
    (
        11,
        [
            0x28, 0xea, 0xc4, 0x0e, 0x45, 0x71, 0xee, 0xe8, 0x1f, 0xb1, 0xd9, 0xfe, 0xfc, 0xfb,
            0xee, 0x18, 0x88, 0x64, 0x4d, 0xff, 0xb7, 0x8b, 0xc7, 0x72, 0x44, 0xaf, 0xf6, 0xff,
            0x8b, 0xdd, 0x59, 0xce,
        ],
    ),
    (
        12,
        [
            0x72, 0xd6, 0xed, 0x1e, 0x53, 0x4b, 0x30, 0x84, 0x1f, 0x74, 0x0d, 0xa8, 0x68, 0x2b,
            0x40, 0xab, 0x02, 0xf2, 0xcc, 0xc0, 0x05, 0x1b, 0x30, 0x2d, 0x53, 0xd3, 0x9f, 0xfc,
            0x4a, 0xb2, 0x51, 0x80,
        ],
    ),
];

#[cfg(test)]
fn lagrange_basis_hash<C: CurveAffine>(basis: &[C]) -> [u8; LAGRANGE_BASIS_HASH_LENGTH] {
    use blake2b_simd::Params as Blake2bParams;

    let mut hasher = Blake2bParams::new()
        .hash_length(LAGRANGE_BASIS_HASH_LENGTH)
        .personal(b"ZakuraOrchardFFT")
        .to_state();
    for point in basis {
        hasher.update(point.to_bytes().as_ref());
    }

    hasher
        .finalize()
        .as_bytes()
        .try_into()
        .expect("configured digest length matches the output array")
}

#[test]
fn selected_lagrange_bases_are_stable() {
    use crate::pasta::EqAffine;

    // `g_lagrange` is the inverse curve-FFT output used to commit directly
    // to evaluation-form polynomials; k = 11 is Orchard's production size.
    // Pin canonical encodings at adjacent depths so an FFT optimization
    // cannot silently change the commitment basis.
    let actual_hashes: Vec<_> = EXPECTED_LAGRANGE_BASIS_HASHES
        .iter()
        .map(|(k, _)| {
            let params = Params::<EqAffine>::new(*k);
            (*k, lagrange_basis_hash(&params.g_lagrange))
        })
        .collect();

    assert_eq!(
        actual_hashes.as_slice(),
        EXPECTED_LAGRANGE_BASIS_HASHES,
        "a pinned Lagrange commitment basis changed"
    );
}

#[test]
fn incorrect_lagrange_basis_does_not_match_hash_pin() {
    use crate::pasta::EqAffine;

    let (k, expected_hash) = EXPECTED_LAGRANGE_BASIS_HASHES[0];
    let params = Params::<EqAffine>::new(k);
    let mut incorrect_basis = params.g_lagrange;
    assert_ne!(incorrect_basis[0], incorrect_basis[1]);
    incorrect_basis[0] = incorrect_basis[1];

    assert_ne!(lagrange_basis_hash(&incorrect_basis), expected_hash);
}

#[cfg(feature = "batch")]
#[test]
fn instance_window_cache_is_shared_by_clones_only() {
    const K: u32 = 6;
    const BASE_COUNT: usize = 10;

    use std::sync::Arc;

    use crate::pasta::EqAffine;

    let params = Arc::new(Params::<EqAffine>::new(K));
    let debug_before = format!("{params:?}");
    let mut serialized_before = vec![];
    params.write(&mut serialized_before).unwrap();

    let tables = std::thread::scope(|scope| {
        (0..4)
            .map(|_| {
                let params = Arc::clone(&params);
                scope.spawn(move || params.instance_window_table(BASE_COUNT))
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect::<Vec<_>>()
    });
    assert_eq!(
        tables[0].len(),
        BASE_COUNT * INSTANCE_WINDOW_ENTRIES_PER_BASE,
    );
    assert!(tables
        .iter()
        .skip(1)
        .all(|table| Arc::ptr_eq(&tables[0], table)));

    let cloned = params.as_ref().clone();
    let cloned_table = cloned.instance_window_table(BASE_COUNT);
    assert!(Arc::ptr_eq(&tables[0], &cloned_table));
    assert_eq!(format!("{params:?}"), debug_before);

    let mut serialized_after = vec![];
    params.write(&mut serialized_after).unwrap();
    assert_eq!(serialized_after, serialized_before);

    let deserialized = Params::<EqAffine>::read(&mut serialized_before.as_slice()).unwrap();
    let smaller_table = params.instance_window_table(BASE_COUNT - 1);
    assert!(Arc::ptr_eq(&tables[0], &smaller_table));

    let larger_table = params.instance_window_table(BASE_COUNT + 1);
    assert!(!Arc::ptr_eq(&tables[0], &larger_table));
    let original_prefix = params.instance_window_table(BASE_COUNT);
    assert!(Arc::ptr_eq(&larger_table, &original_prefix));

    let deserialized_table = deserialized.instance_window_table(BASE_COUNT);
    assert!(!Arc::ptr_eq(&larger_table, &deserialized_table));
}

/// Wrapper type around a blinding factor.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Blind<F>(pub F);

impl<F: Field> Default for Blind<F> {
    fn default() -> Self {
        Blind(F::ONE)
    }
}

impl<F: Field> Add for Blind<F> {
    type Output = Self;

    fn add(self, rhs: Blind<F>) -> Self {
        Blind(self.0 + rhs.0)
    }
}

impl<F: Field> Mul for Blind<F> {
    type Output = Self;

    fn mul(self, rhs: Blind<F>) -> Self {
        Blind(self.0 * rhs.0)
    }
}

impl<F: Field> AddAssign for Blind<F> {
    fn add_assign(&mut self, rhs: Blind<F>) {
        self.0 += rhs.0;
    }
}

impl<F: Field> MulAssign for Blind<F> {
    fn mul_assign(&mut self, rhs: Blind<F>) {
        self.0 *= rhs.0;
    }
}

impl<F: Field> AddAssign<F> for Blind<F> {
    fn add_assign(&mut self, rhs: F) {
        self.0 += rhs;
    }
}

impl<F: Field> MulAssign<F> for Blind<F> {
    fn mul_assign(&mut self, rhs: F) {
        self.0 *= rhs;
    }
}

#[test]
fn test_commit_lagrange_epaffine() {
    const K: u32 = 6;

    use rand::rng;

    use crate::pasta::{EpAffine, Fq};
    let params = Params::<EpAffine>::new(K);
    let domain = super::EvaluationDomain::new(1, K);

    let mut a = domain.empty_lagrange();

    for (i, a) in a.iter_mut().enumerate() {
        *a = Fq::from(i as u64);
    }

    let b = domain.lagrange_to_coeff(a.clone());

    let alpha = Blind(Fq::random(&mut rng()));

    assert_eq!(params.commit(&b, alpha), params.commit_lagrange(&a, alpha));
}

#[test]
fn test_commit_lagrange_eqaffine() {
    const K: u32 = 6;

    use rand::rng;

    use crate::pasta::{EqAffine, Fp};
    let params = Params::<EqAffine>::new(K);
    let domain = super::EvaluationDomain::new(1, K);

    let mut a = domain.empty_lagrange();

    for (i, a) in a.iter_mut().enumerate() {
        *a = Fp::from(i as u64);
    }

    let b = domain.lagrange_to_coeff(a.clone());

    let alpha = Blind(Fp::random(&mut rng()));

    assert_eq!(params.commit(&b, alpha), params.commit_lagrange(&a, alpha));
}

/// Prepared commitment tables must not change a single commitment: armed
/// params (routed through the prepared tables inside a pool within the
/// thread gate, and through the planned multiexp on the ambient pool) agree
/// with independent unarmed params on random polynomials in both bases,
/// including sparse witness-like coefficient patterns.
#[test]
fn prepared_commitments_match_unprepared() {
    const K: u32 = 6;

    use rand::rng;

    use crate::pasta::{EqAffine, Fp};
    // Clones share the preparation caches, so an unarmed control needs its
    // own independently constructed (deterministic) params.
    let armed = Params::<EqAffine>::new(K);
    let unarmed = Params::<EqAffine>::new(K);
    let domain = super::EvaluationDomain::new(1, K);
    let armed_ok = armed.prepare_commitments();
    #[cfg(feature = "orbits")]
    {
        assert!(armed_ok, "Pasta params must arm under the orbits feature");
        assert!(armed.zero_check().is_some());
        assert!(armed.lagrange_table().is_some());
    }
    #[cfg(not(feature = "orbits"))]
    assert!(!armed_ok);

    let mut rng = rng();
    let exercise = |armed: &Params<EqAffine>, unarmed: &Params<EqAffine>, seed: u64| {
        let mut a = domain.empty_lagrange();
        for (i, a) in a.iter_mut().enumerate() {
            // A witness-like mix: zero padding, booleans, small values, and
            // full-width entries.
            *a = match i % 4 {
                0 => Fp::zero(),
                1 => Fp::from((i as u64) & 1),
                2 => Fp::from(seed + i as u64),
                _ => Fp::random(&mut rand::rng()),
            };
        }
        let b = domain.lagrange_to_coeff(a.clone());
        let alpha = Blind(Fp::random(&mut rand::rng()));
        assert_eq!(armed.commit(&b, alpha), unarmed.commit(&b, alpha));
        assert_eq!(
            armed.commit_lagrange(&a, alpha),
            unarmed.commit_lagrange(&a, alpha)
        );
        assert_eq!(armed.commit(&b, alpha), armed.commit_lagrange(&a, alpha));
    };

    // Ambient pool: whatever width the host provides.
    exercise(&armed, &unarmed, Fp::random(&mut rng).to_repr()[0] as u64);
    // Two capped pools: one within the thread gate pins the prepared route
    // itself, and one just past it pins the armed fall-through to the
    // planned multiexp — both regardless of the host's width.
    #[cfg(all(feature = "orbits", feature = "multicore"))]
    for num_threads in [
        msm::PREPARED_MSM_MAX_THREADS,
        msm::PREPARED_MSM_MAX_THREADS + 1,
    ] {
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .expect("test pool must build")
            .install(|| exercise(&armed, &unarmed, 41 + num_threads as u64));
    }
}

#[test]
fn test_opening_proof() {
    const K: u32 = 6;

    use ff::Field;
    use rand::rng;

    use super::{
        commitment::{Blind, Params},
        EvaluationDomain,
    };
    use crate::arithmetic::eval_polynomial;
    use crate::pasta::{EpAffine, Fq};
    use crate::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, Transcript, TranscriptRead, TranscriptWrite,
    };

    let mut rng = rng();

    let params = Params::<EpAffine>::new(K);
    let mut params_buffer = vec![];
    params.write(&mut params_buffer).unwrap();
    let params: Params<EpAffine> = Params::read::<_>(&mut &params_buffer[..]).unwrap();
    // Arm the prepared commitment tables (a no-op without `orbits`): on
    // hosts within the thread gate this routes the commitment below and the
    // verifier's final check through the preparations, so the round trip
    // covers the prepared prover and verifier paths against each other.
    params.prepare_commitments();

    let domain = EvaluationDomain::new(1, K);

    let mut px = domain.empty_coeff();

    for (i, a) in px.iter_mut().enumerate() {
        *a = Fq::from(i as u64);
    }

    let blind = Blind(Fq::random(&mut rng));

    let p = params.commit(&px, blind).to_affine();

    let mut transcript = Blake2bWrite::<Vec<u8>, EpAffine, Challenge255<EpAffine>>::init(vec![]);
    transcript.write_point(p).unwrap();
    let x = transcript.squeeze_challenge_scalar::<()>();
    // Evaluate the polynomial
    let v = eval_polynomial(&px, *x);
    transcript.write_scalar(v).unwrap();

    let (proof, ch_prover) = {
        create_proof(&params, rng, &mut transcript, &px, blind, *x).unwrap();
        let ch_prover = transcript.squeeze_challenge();
        (transcript.finalize(), ch_prover)
    };

    // Verify the opening proof
    let mut transcript = Blake2bRead::<&[u8], EpAffine, Challenge255<EpAffine>>::init(&proof[..]);
    let p_prime = transcript.read_point().unwrap();
    assert_eq!(p, p_prime);
    let x_prime = transcript.squeeze_challenge_scalar::<()>();
    assert_eq!(*x, *x_prime);
    let v_prime = transcript.read_scalar().unwrap();
    assert_eq!(v, v_prime);

    let mut commitment_msm = params.empty_msm();
    commitment_msm.append_term(Field::ONE, p);
    let guard = verify_proof(&params, commitment_msm, &mut transcript, *x, v).unwrap();
    let ch_verifier = transcript.squeeze_challenge();
    assert_eq!(*ch_prover, *ch_verifier);

    // Test guard behavior prior to checking another proof
    {
        // Test use_challenges()
        let msm_challenges = guard.clone().use_challenges();
        assert!(msm_challenges.eval());

        let msm_scaled = guard.clone().use_challenges_with_scale(Fq::from(7));
        assert!(msm_scaled.eval());

        // A valid opening evaluates to the identity with or without scaling,
        // so use a bad opening to check that the scale is actually applied.
        let mut bad_transcript =
            Blake2bRead::<&[u8], EpAffine, Challenge255<EpAffine>>::init(&proof[..]);
        let bad_p = bad_transcript.read_point().unwrap();
        let bad_x = bad_transcript.squeeze_challenge_scalar::<()>();
        let bad_v = bad_transcript.read_scalar().unwrap();
        let mut bad_commitment_msm = params.empty_msm();
        bad_commitment_msm.append_term(Field::ONE, bad_p);
        let bad_guard = verify_proof(
            &params,
            bad_commitment_msm,
            &mut bad_transcript,
            *bad_x,
            bad_v + Fq::ONE,
        )
        .unwrap();

        let rho = Fq::from(7);
        let unscaled = bad_guard.clone().use_challenges();
        assert!(!unscaled.clone().eval());
        let mut expected_scaled = unscaled;
        expected_scaled.scale(rho);
        let mut actual_scaled = bad_guard.use_challenges_with_scale(rho);
        actual_scaled.scale(-Fq::ONE);
        expected_scaled.add_msm(&actual_scaled);
        assert!(expected_scaled.eval());

        // Test use_g()
        let g = guard.compute_g();
        let (msm_g, _accumulator) = guard.clone().use_g(g);
        assert!(msm_g.eval());
    }
}
