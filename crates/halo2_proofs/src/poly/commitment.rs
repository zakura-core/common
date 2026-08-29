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
//! BCMS20 samples $s$ across the entire supported degree range. Since every
//! group message is independently blinded, the mask's only effect on the
//! transcript distribution is through the revealed scalar $c$, which it
//! makes either uniformly random or publicly zero, with the case decided by
//! public challenges alone. The following mask, supported on $k+1$
//! carefully chosen coefficients, gives $c$ the identical distribution. The
//! argument is as follows.
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
//! Sample $\alpha_0, \ldots, \alpha_{k-1}$ uniformly and set
//!
//! $$s(X) = \sum_{t=0}^{k-1} \alpha_t (X^{2^t} - x^{2^t}),$$
//!
//! so that $s(x) = 0$ for every choice of the $\alpha_t$, and $s$ is
//! supported on the $k+1$ indices $\{0, 1, 2, 4, \ldots, 2^{k-1}\}$. Since
//! $\lambda_0 = 1$ and $\lambda_{2^t} = u_{k-1-t}^{-1}$,
//!
//! $$\langle s, \lambda \rangle
//! = \sum_{t=0}^{k-1} \alpha_t (u_{k-1-t}^{-1} - x^{2^t}).$$
//!
//! All group messages before $c$ are independently Pedersen-blinded, so
//! conditioned on the challenges and the group messages, the $\alpha_t$
//! remain uniform. Two cases follow.
//!
//! If $u_{k-1-t}^{-1} \neq x^{2^t}$ for some $t$, then
//! $\langle s, \lambda \rangle$ is a nonzero linear form in the $\alpha_t$,
//! so $c = \langle p, \lambda \rangle - v + \xi \langle s, \lambda \rangle$
//! is uniform.
//!
//! If instead $u_{k-1-t}^{-1} = x^{2^t}$ for every $t$ — the zero case —
//! the product formula gives $\lambda_i = x^i$ for every $i < n$: $\lambda$
//! is the public evaluation functional, and $c = p(x) - v = 0$
//! deterministically.
//!
//! In both cases $c$ reveals nothing about the witness, and which case
//! occurs is decided by public challenges alone, exactly as with a mask
//! sampled across the full degree range. The honest-verifier simulator
//! checks which case the challenges select, setting $c = 0$ in the zero case
//! and sampling $c$ uniformly otherwise; it then samples the final combined
//! blind uniformly, samples all but one group message, and solves the
//! verifier equation for the remaining message using $\xi^{-1}$. This gives
//! the honest transcript distribution. The same random-oracle programming
//! argument as BCMS20 Appendix A.3.1 applies after Fiat-Shamir.
//!
//! By contrast, a mask supported only on a coefficient prefix of length
//! $m < n$ has a genuinely exceptional event: $\lambda_i = x^i$ for $i < m$
//! only, in which $\langle s, \lambda \rangle = 0$ while $\lambda$ is not
//! the evaluation functional, so $c$ is a nontrivial function of the
//! witness. The power-of-two support removes that event at the same cost:
//! the masking commitment is a $(k+2)$-term MSM ($k+1$ coefficients plus one
//! Pedersen blind), thirteen terms for $k = 11$.
//!
//! This argument uses the standard nonzero challenge space from BCMS20, and
//! the overall zero-knowledge distance is governed by ordinary transcript
//! events — zero challenges and unencodable identity points — rather than
//! by the folding-challenge coincidence above (which is simulatable, not
//! exceptional). The implementation aborts if any $u_j = 0$, since it must
//! invert each; a transcript encoding that samples the whole field
//! therefore contributes its existing $O(k/|\mathbb F|)$ abort probability.
//! The event $\xi = 0$ adds at most $1/|\mathbb F|$, and each of the $2k+1$
//! independently blinded group messages — the mask commitment and the $k$
//! left and right points — is the identity, which the transcript refuses to
//! encode, with probability $1/|\mathbb F|$. The honest-verifier
//! statistical distance is thus $O(k/|\mathbb F|)$, and no claim smaller
//! than that is meaningful for the scheme as implemented.
//!
//! [BCMS20]: https://eprint.iacr.org/2020/499

use super::{Coeff, LagrangeCoeff, Polynomial};
#[cfg(any(feature = "multicore", feature = "orbits"))]
use crate::arithmetic::PreparedZeroCheck;
use crate::arithmetic::{CurveAffine, CurveExt, best_fft, best_multiexp, parallelize};
use crate::helpers::CurveRead;
#[cfg(feature = "batch")]
use crate::{INSTANCE_WINDOW_ENTRIES_PER_BASE, InstanceWindowTable, MAX_CACHED_INSTANCE_ROWS};

#[cfg(any(feature = "multicore", feature = "orbits"))]
use core::panic::AssertUnwindSafe;
use ff::{Field, PrimeField};
use group::{Curve, Group};
use std::ops::{Add, AddAssign, Mul, MulAssign};
#[cfg(feature = "batch")]
use std::sync::Mutex;
#[cfg(any(feature = "multicore", feature = "orbits"))]
use std::sync::OnceLock;
#[cfg(any(feature = "batch", feature = "multicore", feature = "orbits"))]
use std::{fmt, sync::Arc};

mod msm;
mod prover;

/// One byte per cached fixed-base window. This spends 255 affine points per
/// scalar-representation byte and evaluates a blind with at most one mixed
/// addition per byte, without doublings.
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const BLIND_WINDOW_BITS: usize = u8::BITS as usize;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const BLIND_WINDOW_ENTRIES: usize = (1 << BLIND_WINDOW_BITS) - 1;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const BLIND_BYTE_ORDER_PROBE: u64 = 0x0102_0304_0506_0708;

/// The `k = 11` SRS shape, whose current Pasta α7 tables remain ahead
/// through all ten cores on the benchmarked Apple M4 systems.
#[cfg(all(
    any(feature = "multicore", feature = "orbits"),
    target_arch = "aarch64",
    target_os = "macos"
))]
const APPLE_TEN_WORKER_PREPARED_COMMITMENT_K: u32 = 11;
#[cfg(all(
    any(feature = "multicore", feature = "orbits"),
    target_arch = "aarch64",
    target_os = "macos"
))]
const APPLE_PREPARED_COMMITMENT_MAX_THREADS: usize = 10;

/// The widest measured pool for prepared prover commitments at `k`.
/// Unmeasured SRS shapes keep the verifier's conservative eight-worker
/// bound. This applies to every prepared backend at `k = 11`; Pasta is
/// currently the only such backend.
#[cfg(any(feature = "multicore", feature = "orbits"))]
fn prepared_commitment_max_threads(k: u32) -> usize {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    if k == APPLE_TEN_WORKER_PREPARED_COMMITMENT_K {
        return APPLE_PREPARED_COMMITMENT_MAX_THREADS;
    }
    let _ = k;
    msm::PREPARED_MSM_MAX_THREADS
}
mod verifier;

pub use msm::MSM;
pub use prover::create_proof;
pub use verifier::{Accumulator, Guard, verify_proof};

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
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    commitment_tables_cache: CommitmentTablesCache<C>,
    #[cfg(feature = "orbits")]
    lagrange_table_cache: ZeroCheckCache<C>,
}

/// A lazily built prepared fixed-base multiexp table — over `[g..., w, u]`
/// for [`Params::prepare_zero_checks`], or `[g_lagrange..., w, u]` for the
/// Lagrange half of [`Params::prepare_commitments`] — shared across clones
/// of the params that hold it. The first non-panicking result (including a
/// backend decline) is retained. Never serialized; rebuilt on demand after
/// `read`. The cached handle is marked unwind-safe because [`OnceLock`] does
/// not publish a panicking initializer and the cache never mutates or replaces
/// a published handle.
#[cfg(feature = "orbits")]
#[derive(Clone)]
struct ZeroCheckCache<C: CurveAffine>(
    #[allow(clippy::type_complexity)]
    Arc<OnceLock<Option<AssertUnwindSafe<Arc<dyn PreparedZeroCheck<C::CurveExt>>>>>>,
);

#[cfg(feature = "orbits")]
impl<C: CurveAffine> Default for ZeroCheckCache<C> {
    fn default() -> Self {
        Self(Arc::new(OnceLock::new()))
    }
}

#[cfg(feature = "orbits")]
impl<C: CurveAffine> ZeroCheckCache<C> {
    fn initialize(
        &self,
        initialize: impl FnOnce() -> Option<Box<dyn PreparedZeroCheck<C::CurveExt>>>,
    ) -> bool {
        self.0
            .get_or_init(|| initialize().map(|prepared| AssertUnwindSafe(Arc::from(prepared))))
            .is_some()
    }

    fn get(&self) -> Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>> {
        self.0
            .get()
            .and_then(Option::as_ref)
            .map(|prepared| Arc::clone(&prepared.0))
    }
}

#[cfg(feature = "orbits")]
impl<C: CurveAffine> fmt::Debug for ZeroCheckCache<C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let armed = matches!(self.0.get(), Some(Some(_)));
        formatter
            .debug_tuple("ZeroCheckCache")
            .field(&armed)
            .finish()
    }
}

/// The no-orbits prover's exact-`n` coefficient and Lagrange preparations.
/// One lock makes their initialization atomic and prevents concurrent calls
/// from duplicating the two large table builds. The cached handles are marked
/// unwind-safe because [`OnceLock`] does not publish a panicking initializer and
/// the cache never mutates or replaces published handles.
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[derive(Clone)]
struct CommitmentTablesCache<C: CurveAffine>(
    #[allow(clippy::type_complexity)]
    Arc<
        OnceLock<
            Option<(
                AssertUnwindSafe<Arc<dyn PreparedZeroCheck<C::CurveExt>>>,
                AssertUnwindSafe<Arc<dyn PreparedZeroCheck<C::CurveExt>>>,
                Arc<BlindTable<C>>,
            )>,
        >,
    >,
);

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
impl<C: CurveAffine> Default for CommitmentTablesCache<C> {
    fn default() -> Self {
        Self(Arc::new(OnceLock::new()))
    }
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
impl<C: CurveAffine> CommitmentTablesCache<C> {
    #[allow(clippy::type_complexity)]
    fn initialize(
        &self,
        initialize: impl FnOnce() -> Option<(
            Box<dyn PreparedZeroCheck<C::CurveExt>>,
            Box<dyn PreparedZeroCheck<C::CurveExt>>,
            BlindTable<C>,
        )>,
    ) -> bool {
        self.0
            .get_or_init(|| {
                initialize().map(|(coefficient, lagrange, blind)| {
                    (
                        AssertUnwindSafe(Arc::from(coefficient)),
                        AssertUnwindSafe(Arc::from(lagrange)),
                        Arc::new(blind),
                    )
                })
            })
            .is_some()
    }

    fn coefficient(&self) -> Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>> {
        self.0
            .get()
            .and_then(Option::as_ref)
            .map(|(coefficient, _, _)| Arc::clone(&coefficient.0))
    }

    fn lagrange(&self) -> Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>> {
        self.0
            .get()
            .and_then(Option::as_ref)
            .map(|(_, lagrange, _)| Arc::clone(&lagrange.0))
    }

    fn blind(&self) -> Option<Arc<BlindTable<C>>> {
        self.0
            .get()
            .and_then(Option::as_ref)
            .map(|(_, _, blind)| Arc::clone(blind))
    }
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
impl<C: CurveAffine> fmt::Debug for CommitmentTablesCache<C> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let armed = matches!(self.0.get(), Some(Some(_)));
        formatter
            .debug_tuple("CommitmentTablesCache")
            .field(&armed)
            .finish()
    }
}

/// A fixed-window table for the commitment blinding generator.
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
struct BlindTable<C: CurveAffine> {
    base: C,
    points: Vec<C>,
    windows: usize,
    byte_order: BlindScalarByteOrder,
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[derive(Clone, Copy)]
enum BlindScalarByteOrder {
    LittleEndian,
    BigEndian,
    Unsupported,
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
impl<C: CurveAffine> BlindTable<C> {
    fn new(base: C) -> Self {
        let windows = <C::Scalar as PrimeField>::Repr::default().as_ref().len();
        let mut projective = Vec::with_capacity(windows * BLIND_WINDOW_ENTRIES);
        let mut window_base = C::Curve::from(base);
        for _ in 0..windows {
            let mut multiple = window_base;
            for _ in 0..BLIND_WINDOW_ENTRIES {
                projective.push(multiple);
                multiple += window_base;
            }
            for _ in 0..BLIND_WINDOW_BITS {
                window_base = window_base.double();
            }
        }
        let mut points = vec![C::identity(); projective.len()];
        C::Curve::batch_normalize(&projective, &mut points);

        let probe = C::Scalar::from(BLIND_BYTE_ORDER_PROBE);
        let probe_repr = probe.to_repr();
        let probe_bytes = probe_repr.as_ref();
        let little = Self::decode(probe_bytes.iter().rev().copied()) == probe;
        let big = Self::decode(probe_bytes.iter().copied()) == probe;
        let byte_order = match (little, big) {
            (true, false) => BlindScalarByteOrder::LittleEndian,
            (false, true) => BlindScalarByteOrder::BigEndian,
            _ => BlindScalarByteOrder::Unsupported,
        };

        Self {
            base,
            points,
            windows,
            byte_order,
        }
    }

    fn decode(bytes: impl Iterator<Item = u8>) -> C::Scalar {
        let radix = C::Scalar::from(1u64 << BLIND_WINDOW_BITS);
        bytes.fold(C::Scalar::ZERO, |acc, byte| {
            acc * radix + C::Scalar::from(u64::from(byte))
        })
    }

    /// Multiplies the cached base by `scalar`.
    ///
    /// This is variable-time in `scalar`: it skips zero digits and indexes the
    /// table by each nonzero digit. The prover's commitment MSMs already accept
    /// variable-time evaluation of their secret inputs.
    fn multiply(&self, scalar: C::Scalar) -> C::Curve {
        let repr = scalar.to_repr();
        let bytes = repr.as_ref();
        if bytes.len() != self.windows {
            return C::Curve::from(self.base) * scalar;
        }

        // [`PrimeField::Repr`] is opaque and has implementation-specific
        // endianness. The probe selects a candidate byte order, and every
        // multiplication verifies its digits before using the table. An
        // exotic representation safely falls back to native multiplication.
        let little = match self.byte_order {
            BlindScalarByteOrder::LittleEndian => true,
            BlindScalarByteOrder::BigEndian => false,
            BlindScalarByteOrder::Unsupported => {
                return C::Curve::from(self.base) * scalar;
            }
        };
        let decoded = if little {
            Self::decode(bytes.iter().rev().copied())
        } else {
            Self::decode(bytes.iter().copied())
        };
        if decoded != scalar {
            return C::Curve::from(self.base) * scalar;
        }

        let mut acc = C::Curve::identity();
        for (position, &digit) in bytes.iter().enumerate() {
            if digit == 0 {
                continue;
            }
            let window = if little {
                position
            } else {
                self.windows - position - 1
            };
            acc += self.points[window * BLIND_WINDOW_ENTRIES + usize::from(digit) - 1];
        }
        acc
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
            #[cfg(all(feature = "multicore", not(feature = "orbits")))]
            commitment_tables_cache: CommitmentTablesCache::default(),
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
        // Like `MSM::eval`, the routing is thread-gated: past the measured
        // bound for this SRS shape, the planned multiexp is retained.
        #[cfg(feature = "orbits")]
        if crate::multicore::current_num_threads() <= prepared_commitment_max_threads(self.k)
            && let Some(prepared) = self.zero_check()
        {
            let n = self.n as usize;
            if prepared.terms() == n + 2 && poly.len() == n {
                let mut fixed = Vec::with_capacity(n + 2);
                fixed.extend(poly.iter());
                fixed.push(r.0);
                fixed.push(C::Scalar::ZERO);
                return prepared.multiexp_with_terms_vartime(&fixed, &[]);
            }
        }

        // Without `orbits`, the prepared table covers exactly `g`; a small
        // fixed-window table handles the blind without a one-term MSM.
        #[cfg(all(feature = "multicore", not(feature = "orbits")))]
        if crate::multicore::current_num_threads() <= prepared_commitment_max_threads(self.k)
            && let (Some(prepared), Some(blind_table)) =
                (self.commitment_table(), self.blind_table())
        {
            let n = self.n as usize;
            if prepared.terms() == n && poly.len() == n {
                let mut commitment = prepared.multiexp_with_terms_vartime(poly, &[]);
                commitment += blind_table.multiply(r.0);
                return commitment;
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
        if crate::multicore::current_num_threads() <= prepared_commitment_max_threads(self.k)
            && let Some(prepared) = self.lagrange_table()
        {
            let n = self.n as usize;
            if prepared.terms() == n + 2 && poly.len() == n {
                let mut fixed = Vec::with_capacity(n + 2);
                fixed.extend(poly.iter());
                fixed.push(r.0);
                fixed.push(C::Scalar::ZERO);
                return prepared.multiexp_with_terms_vartime(&fixed, &[]);
            }
        }

        // The exact-`n` Lagrange table mirrors the coefficient route above.
        #[cfg(all(feature = "multicore", not(feature = "orbits")))]
        if crate::multicore::current_num_threads() <= prepared_commitment_max_threads(self.k)
            && let (Some(prepared), Some(blind_table)) = (self.lagrange_table(), self.blind_table())
        {
            let n = self.n as usize;
            if prepared.terms() == n && poly.len() == n {
                let mut commitment = prepared.multiexp_with_terms_vartime(poly, &[]);
                commitment += blind_table.multiply(r.0);
                return commitment;
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
            #[cfg(all(feature = "multicore", not(feature = "orbits")))]
            commitment_tables_cache: CommitmentTablesCache::default(),
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
    /// The routing is thread-aware: on pools wider than eight effective
    /// threads, the unprepared planner out-scales the prepared evaluation
    /// (measured end-to-end on 16- and 32-thread pools), so `eval` falls
    /// back to the plain multiexp there and arming is never a pessimization.
    /// A wide-pool validator simply amortizes the preparation over the
    /// verifications that run on narrower pools.
    ///
    /// Preparation costs hundreds of milliseconds and tens of mebibytes
    /// at typical `k`, amortized across every subsequent verification
    /// with these params (batch verification folds many proofs into a
    /// single final check, so it also pays just one). The cache is shared
    /// with all clones of these params. Concurrent and repeat calls share
    /// the same initialization attempt, including a backend decline. The
    /// cache is never serialized, so call this again after [`Params::read`].
    /// Call this once before entering concurrent Rayon work that uses these
    /// params. Concurrent callers outside that pool safely wait for and share
    /// the same attempt; fanning a cold call out across the worker pool can
    /// occupy its other workers and serialize the initializer's parallel work.
    ///
    /// Returns whether a prepared check was actually built and cached.
    /// `false` means arming was a no-op — the curve has no prepared
    /// backend, the backend declined (its prepared table for this SRS would
    /// exceed its internal footprint budget; on Pasta this begins at
    /// `k = 13`), or the `orbits` feature (disabled by default) is off — and
    /// verification simply keeps evaluating the plain multiexp. Callers may
    /// ignore the result; long-lived validators that expect the speedup can
    /// assert or log it.
    pub fn prepare_zero_checks(&self) -> bool {
        #[cfg(feature = "orbits")]
        {
            self.zero_check_cache.initialize(|| {
                let mut bases = Vec::with_capacity(self.g.len() + 2);
                bases.extend_from_slice(&self.g);
                bases.push(self.w);
                bases.push(self.u);
                C::CurveExt::try_prepare_zero_check(&bases)
            })
        }
        #[cfg(not(feature = "orbits"))]
        {
            false
        }
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn commitment_table(&self) -> Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>> {
        self.commitment_tables_cache.coefficient()
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn blind_table(&self) -> Option<Arc<BlindTable<C>>> {
        self.commitment_tables_cache.blind()
    }

    /// The cached prepared zero-check, if [`Self::prepare_zero_checks`]
    /// built one.
    #[cfg(feature = "orbits")]
    pub(crate) fn zero_check(&self) -> Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>> {
        self.zero_check_cache.get()
    }

    /// Builds and caches prepared fixed-base multiexp tables for the prover's
    /// commitments. With `orbits`, the coefficient table over `[g..., w, u]`
    /// is shared with [`Self::prepare_zero_checks`], and the Lagrange table
    /// covers `[g_lagrange..., w, u]`. Without `orbits`, the two tables cover
    /// exactly `g` and `g_lagrange`, plus a fixed-window table over `w`. This
    /// evaluates each blind without a one-term MSM while keeping the polynomial
    /// slice borrowed.
    ///
    /// Both commit methods use the tables on pools of at most eight effective
    /// threads. Orchard-sized (`k = 11`) tables on AArch64 macOS extend that
    /// bound to ten, where end-to-end proving stays ahead on the benchmarked
    /// M4 system. Wider pools and unmeasured SRS shapes keep the planned
    /// multiexp. Measurements covered full-width and witness-like (boolean,
    /// byte, zero-padded) coefficient distributions.
    ///
    /// The two α7 tables account for about 24.8 MiB at `k = 11`; the no-orbits
    /// fixed-window table adds approximately 0.5 MiB for a 32-byte scalar
    /// representation. Concurrent and repeat calls share their initialization
    /// attempts, including a backend decline. Without `orbits`, one atomic
    /// initialization prevents any table from being exposed until all three
    /// have built. The caches are shared with all clones and never serialized,
    /// so call again after [`Params::read`]. Returns whether preparation is
    /// armed. Without `orbits`, this also requires the default `multicore`
    /// feature.
    ///
    /// Call this once before entering concurrent Rayon work that uses these
    /// params. Concurrent callers outside that pool safely wait for and share
    /// the same attempt; fanning a cold call out across the worker pool can
    /// occupy its other workers and serialize the initializer's parallel work.
    pub fn prepare_commitments(&self) -> bool {
        #[cfg(feature = "orbits")]
        {
            if !self.prepare_zero_checks() {
                // Both tables have the same term count, so a coefficient
                // decline means the Lagrange build would decline too.
                return false;
            }
            self.lagrange_table_cache.initialize(|| {
                let mut bases = Vec::with_capacity(self.g_lagrange.len() + 2);
                bases.extend_from_slice(&self.g_lagrange);
                bases.push(self.w);
                bases.push(self.u);
                C::CurveExt::try_prepare_zero_check(&bases)
            })
        }
        #[cfg(all(feature = "multicore", not(feature = "orbits")))]
        {
            self.commitment_tables_cache.initialize(|| {
                let coefficient = C::CurveExt::try_prepare_zero_check(&self.g)?;
                let lagrange = C::CurveExt::try_prepare_zero_check(&self.g_lagrange)?;
                let blind = BlindTable::new(self.w);
                Some((coefficient, lagrange, blind))
            })
        }
        #[cfg(all(not(feature = "multicore"), not(feature = "orbits")))]
        {
            false
        }
    }

    /// The cached Lagrange-basis prepared table, if
    /// [`Self::prepare_commitments`] built one.
    #[cfg(any(feature = "multicore", feature = "orbits"))]
    pub(crate) fn lagrange_table(&self) -> Option<Arc<dyn PreparedZeroCheck<C::CurveExt>>> {
        #[cfg(feature = "orbits")]
        {
            self.lagrange_table_cache.get()
        }
        #[cfg(all(feature = "multicore", not(feature = "orbits")))]
        {
            self.commitment_tables_cache.lagrange()
        }
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
    assert!(
        tables
            .iter()
            .skip(1)
            .all(|table| Arc::ptr_eq(&tables[0], table))
    );

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

#[cfg(feature = "orbits")]
#[test]
fn prepared_caches_initialize_once_across_clones() {
    const K: u32 = 4;
    const CALLERS: usize = 4;

    use std::sync::{
        Arc, Barrier,
        atomic::{AtomicUsize, Ordering},
    };

    use crate::pasta::{Eq, EqAffine};

    let params = Arc::new(Params::<EqAffine>::new(K));
    let mut bases = Vec::with_capacity(params.g.len() + 2);
    bases.extend_from_slice(&params.g);
    bases.push(params.w);
    bases.push(params.u);
    let bases = Arc::new(bases);
    let attempts = AtomicUsize::new(0);
    let start = Barrier::new(CALLERS);

    let prepared = std::thread::scope(|scope| {
        (0..CALLERS)
            .map(|_| {
                let bases = Arc::clone(&bases);
                let cache = params.zero_check_cache.clone();
                let attempts = &attempts;
                let start = &start;
                scope.spawn(move || {
                    start.wait();
                    assert!(cache.initialize(|| {
                        attempts.fetch_add(1, Ordering::Relaxed);
                        Eq::try_prepare_zero_check(bases.as_slice())
                    }));
                    cache.get().expect("the preparation succeeded")
                })
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect::<Vec<_>>()
    });
    assert_eq!(attempts.load(Ordering::Relaxed), 1);
    assert!(
        prepared
            .iter()
            .skip(1)
            .all(|other| Arc::ptr_eq(&prepared[0], other))
    );

    // The coefficient preparation above is shared through `Params::clone`.
    // Racing full preparation then initializes only the Lagrange table.
    let cloned = Arc::new(params.as_ref().clone());
    let start = Barrier::new(CALLERS);
    let tables = std::thread::scope(|scope| {
        (0..CALLERS)
            .map(|_| {
                let cloned = Arc::clone(&cloned);
                let start = &start;
                scope.spawn(move || {
                    start.wait();
                    assert!(cloned.prepare_commitments());
                    (
                        cloned.zero_check().expect("coefficient table is armed"),
                        cloned.lagrange_table().expect("Lagrange table is armed"),
                    )
                })
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect::<Vec<_>>()
    });
    assert!(tables.iter().skip(1).all(|(coefficient, lagrange)| {
        Arc::ptr_eq(&tables[0].0, coefficient) && Arc::ptr_eq(&tables[0].1, lagrange)
    }));

    let coefficient = cloned.zero_check().unwrap();
    let lagrange = cloned.lagrange_table().unwrap();
    assert!(cloned.prepare_commitments());
    assert!(Arc::ptr_eq(&coefficient, &cloned.zero_check().unwrap()));
    assert!(Arc::ptr_eq(&lagrange, &cloned.lagrange_table().unwrap()));
}

#[cfg(feature = "orbits")]
#[test]
fn prepared_cache_memoizes_decline_and_retries_panic() {
    use std::{
        panic::catch_unwind,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use crate::pasta::EqAffine;

    fn assert_unwind_safe<T: std::panic::RefUnwindSafe + std::panic::UnwindSafe>() {}

    assert_unwind_safe::<Params<EqAffine>>();

    let declined = ZeroCheckCache::<EqAffine>::default();
    let attempts = AtomicUsize::new(0);
    for _ in 0..2 {
        assert!(!declined.initialize(|| {
            attempts.fetch_add(1, Ordering::Relaxed);
            None
        }));
    }
    assert_eq!(attempts.load(Ordering::Relaxed), 1);
    assert!(declined.get().is_none());

    let panicked = ZeroCheckCache::<EqAffine>::default();
    let result = catch_unwind(|| panicked.initialize(|| panic!()));
    assert!(result.is_err());
    assert!(!panicked.initialize(|| None));
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn commitment_tables_cache_initializes_once_across_clones() {
    const K: u32 = 4;
    const CALLERS: usize = 4;

    use std::sync::{
        Arc, Barrier,
        atomic::{AtomicUsize, Ordering},
    };

    use crate::pasta::{Eq, EqAffine};

    let params = Params::<EqAffine>::new(K);
    let coefficient_bases = Arc::new(params.g.clone());
    let lagrange_bases = Arc::new(params.g_lagrange.clone());
    let blind_base = params.w;
    let cache = params.commitment_tables_cache.clone();
    let attempts = AtomicUsize::new(0);
    let start = Barrier::new(CALLERS);

    let tables = std::thread::scope(|scope| {
        (0..CALLERS)
            .map(|_| {
                let coefficient_bases = Arc::clone(&coefficient_bases);
                let lagrange_bases = Arc::clone(&lagrange_bases);
                let cache = cache.clone();
                let attempts = &attempts;
                let start = &start;
                scope.spawn(move || {
                    start.wait();
                    assert!(cache.initialize(|| {
                        attempts.fetch_add(1, Ordering::Relaxed);
                        let coefficient = Eq::try_prepare_zero_check(coefficient_bases.as_slice())?;
                        let lagrange = Eq::try_prepare_zero_check(lagrange_bases.as_slice())?;
                        let blind = BlindTable::new(blind_base);
                        Some((coefficient, lagrange, blind))
                    }));
                    (
                        cache.coefficient().expect("coefficient table is armed"),
                        cache.lagrange().expect("Lagrange table is armed"),
                        cache.blind().expect("blind table is armed"),
                    )
                })
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect::<Vec<_>>()
    });

    assert_eq!(attempts.load(Ordering::Relaxed), 1);
    assert!(tables.iter().skip(1).all(|(coefficient, lagrange, blind)| {
        Arc::ptr_eq(&tables[0].0, coefficient)
            && Arc::ptr_eq(&tables[0].1, lagrange)
            && Arc::ptr_eq(&tables[0].2, blind)
    }));
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn commitment_tables_cache_memoizes_decline_and_retries_panic() {
    use std::{
        panic::catch_unwind,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use crate::pasta::{Eq, EqAffine};

    fn assert_unwind_safe<T: std::panic::RefUnwindSafe + std::panic::UnwindSafe>() {}

    assert_unwind_safe::<Params<EqAffine>>();

    let declined = CommitmentTablesCache::<EqAffine>::default();
    let attempts = AtomicUsize::new(0);
    for _ in 0..2 {
        assert!(!declined.initialize(|| {
            attempts.fetch_add(1, Ordering::Relaxed);
            None
        }));
    }
    assert_eq!(attempts.load(Ordering::Relaxed), 1);
    assert!(declined.coefficient().is_none());
    assert!(declined.lagrange().is_none());
    assert!(declined.blind().is_none());

    let params = Params::<EqAffine>::new(4);
    let panicked = CommitmentTablesCache::<EqAffine>::default();
    let result = catch_unwind(|| panicked.initialize(|| panic!("test initialization panic")));
    assert!(result.is_err());
    assert!(panicked.initialize(|| {
        let coefficient = Eq::try_prepare_zero_check(&params.g)?;
        let lagrange = Eq::try_prepare_zero_check(&params.g_lagrange)?;
        let blind = BlindTable::new(params.w);
        Some((coefficient, lagrange, blind))
    }));
    assert!(panicked.coefficient().is_some());
    assert!(panicked.lagrange().is_some());
    assert!(panicked.blind().is_some());
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

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn blind_table_matches_native_multiplication() {
    use rand::{SeedableRng, rngs::StdRng};

    use crate::pasta::{EpAffine, EqAffine};

    fn exercise<C: CurveAffine>(base: C) {
        let mut table = BlindTable::new(base);
        let little = match table.byte_order {
            BlindScalarByteOrder::LittleEndian => true,
            BlindScalarByteOrder::BigEndian => false,
            BlindScalarByteOrder::Unsupported => {
                panic!("Pasta scalar representations must have a supported byte order")
            }
        };
        let mut rng = StdRng::seed_from_u64(0x626c_696e_642d_6d73);
        let mut scalars = vec![
            C::Scalar::ZERO,
            C::Scalar::ONE,
            -C::Scalar::ONE,
            C::Scalar::from(BLIND_BYTE_ORDER_PROBE),
        ];
        for exponent in [8, 16, 24, 32, 64, 128, 248] {
            let radix_power = C::Scalar::from(2).pow_vartime([exponent]);
            scalars.extend([
                radix_power - C::Scalar::ONE,
                radix_power,
                radix_power + C::Scalar::ONE,
            ]);
        }
        scalars.extend((0..16).map(|_| C::Scalar::random(&mut rng)));

        for scalar in scalars {
            let repr = scalar.to_repr();
            let bytes = repr.as_ref();
            let decoded = if little {
                BlindTable::<C>::decode(bytes.iter().rev().copied())
            } else {
                BlindTable::<C>::decode(bytes.iter().copied())
            };
            assert_eq!(decoded, scalar, "Pasta scalar digits must decode");
            assert_eq!(
                table.multiply(scalar),
                C::Curve::from(base) * scalar,
                "fixed blind multiplication must match native multiplication"
            );
        }

        let fallback_scalar = C::Scalar::from(BLIND_BYTE_ORDER_PROBE);
        table.byte_order = BlindScalarByteOrder::Unsupported;
        assert_eq!(
            table.multiply(fallback_scalar),
            C::Curve::from(base) * fallback_scalar,
            "an unsupported representation must use native multiplication"
        );

        table.byte_order = if little {
            BlindScalarByteOrder::LittleEndian
        } else {
            BlindScalarByteOrder::BigEndian
        };
        table.windows += 1;
        assert_eq!(
            table.multiply(fallback_scalar),
            C::Curve::from(base) * fallback_scalar,
            "a representation-length mismatch must use native multiplication"
        );
    }

    exercise(Params::<EpAffine>::new(3).w);
    exercise(Params::<EqAffine>::new(3).w);
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn blind_table_cache_is_shared_by_clones_and_not_serialized() {
    use crate::pasta::EqAffine;

    let params = Params::<EqAffine>::new(3);
    let mut serialized_before = vec![];
    params.write(&mut serialized_before).unwrap();
    assert!(params.blind_table().is_none());
    assert!(params.prepare_commitments());
    let table = params.blind_table().unwrap();

    let cloned_table = params.clone().blind_table().unwrap();
    assert!(Arc::ptr_eq(&table, &cloned_table));

    let mut serialized_after = vec![];
    params.write(&mut serialized_after).unwrap();
    assert_eq!(serialized_before, serialized_after);

    let deserialized = Params::<EqAffine>::read(&mut serialized_before.as_slice()).unwrap();
    assert!(deserialized.blind_table().is_none());
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
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    {
        assert!(armed_ok, "Pasta commitment tables must prepare");
        assert!(!armed.prepare_zero_checks());
        let coefficient = armed.commitment_table().unwrap();
        let lagrange = armed.lagrange_table().unwrap();
        let blind = armed.blind_table().unwrap();
        let cloned = armed.clone();
        assert!(cloned.prepare_commitments());
        assert!(Arc::ptr_eq(
            &coefficient,
            &cloned.commitment_table().unwrap()
        ));
        assert!(Arc::ptr_eq(&lagrange, &cloned.lagrange_table().unwrap()));
        assert!(Arc::ptr_eq(&blind, &cloned.blind_table().unwrap()));
    }
    #[cfg(all(not(feature = "multicore"), not(feature = "orbits")))]
    assert!(!armed_ok, "preparation stays disabled without multicore");

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
    #[cfg(feature = "multicore")]
    for num_threads in [
        prepared_commitment_max_threads(armed.k),
        prepared_commitment_max_threads(armed.k) + 1,
    ] {
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .expect("test pool must build")
            .install(|| exercise(&armed, &unarmed, 41 + num_threads as u64));
    }
}

#[cfg(any(feature = "multicore", feature = "orbits"))]
#[test]
fn prepared_commitment_thread_policy_is_scoped() {
    assert_eq!(
        prepared_commitment_max_threads(4),
        msm::PREPARED_MSM_MAX_THREADS
    );
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    {
        assert_eq!(
            prepared_commitment_max_threads(APPLE_TEN_WORKER_PREPARED_COMMITMENT_K),
            APPLE_PREPARED_COMMITMENT_MAX_THREADS
        );
        assert_eq!(
            prepared_commitment_max_threads(APPLE_TEN_WORKER_PREPARED_COMMITMENT_K + 1),
            msm::PREPARED_MSM_MAX_THREADS
        );
    }
}

#[test]
fn test_opening_proof() {
    const K: u32 = 6;

    use ff::Field;
    use rand::rng;

    use super::{
        EvaluationDomain,
        commitment::{Blind, Params},
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
    // Arm the prepared commitment tables. Within the thread gate, multicore
    // builds route the commitment below through them; with `orbits`, the
    // verifier's final check is prepared too, while without it the verifier
    // keeps its plain path. Either way the round trip covers the armed prover.
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
