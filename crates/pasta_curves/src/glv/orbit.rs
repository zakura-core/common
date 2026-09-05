//! Eisenstein-orbit Pippenger: a dense multiscalar-multiplication backend
//! that buckets **joint** GLV digits over $\mathbf{Z}[\omega]$.
//!
//! The Signed-Booth backend in the parent module splits every scalar as
//! $k = k_1 + k_2\lambda$ and feeds the two 127-bit halves through ordinary
//! signed windows, so each window sees up to two point assignments per
//! scalar and $2^{c-1}$ buckets. This backend instead keeps the pair as one
//! Eisenstein integer $z = k_1 + k_2\omega$ ($\omega^2 + \omega + 1 = 0$,
//! with $\omega$ acting on the curve as the cube-root endomorphism $\phi$)
//! and recodes it in radix $B = 2^c$ directly over $\mathbf{Z}[\omega]$:
//!
//! $$z = \sum_j B^j d_j, \qquad d_j \in \mathbf{Z}[\omega].$$
//!
//! Every nonzero digit factors uniquely (up to the 2-torsion classes below)
//! as $d = u\delta$ with $u \in U = \{\pm1, \pm\omega, \pm\omega^2\}$ and
//! $\delta$ a canonical representative of its unit orbit, so a window needs
//! only one bucket per *orbit*: $(B^2 + 2)/6$ buckets instead of the
//! $2^{c-1}$-per-half of the Booth backend, and one assignment per scalar
//! per window instead of two. The unit is applied to the stored point for
//! free — $[\pm\omega^e]P = (\zeta^e x, \pm y)$ selects one of three
//! precomputed x-rotations and optionally negates y.
//!
//! # The canonical wedge
//!
//! Orbit representatives are drawn from the wedge
//!
//! $$D_B = \{a + b\omega : a > b \ge 0,\; 2a - b \le B,\; a + b < B\},$$
//!
//! which contains exactly $(B^2 + 2)/6$ points. Its six unit rotations tile
//! the $B^2 - 1$ nonzero residue classes of $\mathbf{Z}[\omega]/B$ exactly:
//! by Burnside's lemma the unit action has $(B^2 + 8)/6$ orbits including
//! zero ($-1$ fixes the four 2-torsion classes; the other nonidentity units
//! fix only zero, since $\omega - 1$ and $\omega^2 - 1$ have odd norm and
//! are invertible mod $2^c$). The three nonzero 2-torsion classes form one
//! orbit of size 3 whose representative $(B/2, 0)$ admits two unit
//! factorizations; both land in the same bucket, so either digit choice is
//! correct. The [`OrbitParams`] constructor rebuilds this tiling from first
//! principles on every use and asserts exact coverage.
//!
//! # Recoding
//!
//! Each step reads the residue $(a \bmod B, b \bmod B)$, emits the unique
//! canonical digit $d = u\delta$ in that class, and replaces $z$ by
//! $(z - d)/B$ — computed as `(a >> c) + (da < 0)` per coefficient, which is
//! exact (the digit is congruent to the value mod $B$ componentwise) and
//! cannot overflow `i128` where a literal `a - da` at magnitudes near
//! $2^{127}$ could. Digit coefficients are bounded by
//! $\lfloor(2B - 1)/3\rfloor < B$, so coefficient magnitudes contract by
//! $|a'| \le (|a| + \lfloor(2B-1)/3\rfloor)/B$ per step; iterating that bound
//! from $2^{127} - 1$ (see [`window_count`]) proves the recoding of any GLV
//! half pair terminates within 43/33/26/22 windows for $c = 3/4/5/6$
//! (re-derived exhaustively by the `window_count_is_exact` test).
//!
//! # The hexagonal weighted-bucket reducer
//!
//! A window's result is $\sum_{\delta} [\delta] Q_\delta$ with
//! two-dimensional weights, so Pippenger's running-sum trick does not apply
//! directly. Instead the wedge carries a spanning tree with parent map
//!
//! $$p(a, b) = \begin{cases}(a - 1, b) & a > 2b\\ (a-1, b-1) & a \le 2b\end{cases}$$
//!
//! whose every edge has difference $1$ or $1 + \omega$ (root $(1,0)$,
//! parent edge to $0$). Accumulating subtree sums $T_\delta$ children-first
//! and totalling them by edge label as $A$ (difference 1) and $H$
//! (difference $1 + \omega$), path telescoping gives
//!
//! $$\sum_\delta [\delta] Q_\delta = A + [1 + \omega]H = A - \phi^2(H),$$
//!
//! since $1 + \omega = -\omega^2$. The cost is $2m - 2$ group additions plus
//! one endomorphism application for $m$ buckets, against $2 \cdot 2^{c-1}$
//! per *half*-window for the Booth reducer.
//!
//! Bucket contents are still accumulated with the parent module's batched
//! affine tree reduction ([`super::reduce_affine_buckets`]); only the
//! $2m - 2$ weighted additions here run on projective accumulators.
//!
//! This backend is selected by the cost model in [`super::plan_multiexp`].
//! Measured against the Signed-Booth backend on 32-core x86-64 (portable
//! field backend; interleaved samples — an earlier sequential harness
//! inflated the first curve's serial Booth column, see
//! `msm_backend_timings`), serial full-width MSMs run at parity within
//! ±2% from 512 to 8,192 terms and +4–5% ahead at 16,384 — one visit per
//! scalar per window and ~25% fewer bucket states buy back its costlier
//! weighted reducer — while the real wins are parallel, where its 22–33
//! windows expose more independent tasks than Booth's 10–16:
//! +10..+41% at 4–16 workers on mid-to-large sizes and +30..+54% on
//! saturated 32-worker pools. Booth keeps small parallel MSMs.

use alloc::vec::Vec;

use ff::Field;
#[cfg(feature = "orbits")]
use group::CurveAffine as _;
#[cfg(all(feature = "multicore", feature = "orbits"))]
use maybe_rayon::prelude::*;

#[cfg(feature = "orbits")]
use super::MagnitudeProfile;
use super::{
    AffinePoint, GLV_COMPONENT_BITS, GlvParams, SignedMagnitude, private, reduce_affine_buckets,
};

/// The window widths [`multiexp`] supports. Wider than 6 needs
/// $(4^c + 2)/6 > 2731$ buckets and only approaches break-even at sizes
/// where the Booth backend already wins on its cheaper reducer.
pub(super) const MIN_WINDOW_BITS: usize = 3;
/// See [`MIN_WINDOW_BITS`].
pub(super) const MAX_WINDOW_BITS: usize = 6;
/// The narrowest width [`estimated_costs`] will price for the planner.
/// Width 3 stays implemented and tested, but its 43 windows of
/// $(4^3 + 2)/6 = 11$ buckets only ever modeled ahead on MSMs of a few
/// hundred terms, where they measured 4–17% *behind* the Booth backend
/// (per-window overhead dominates 200-odd visits); planning starts at 4.
#[cfg(feature = "orbits")]
pub(super) const PLAN_MIN_WINDOW_BITS: usize = 4;
/// The smallest MSM [`estimated_costs`] will price for the planner. At 256
/// terms the backend's fixed per-window costs measured it 2–7% behind
/// Booth at low thread counts (sub-millisecond, noise-prone cells); from
/// 512 terms up it wins. This gates on the *term count*, not liveness —
/// sparse-but-large MSMs stay profitable (witness-shaped 2048-term inputs
/// measured +16..20% over Booth).
#[cfg(feature = "orbits")]
pub(super) const PLAN_MIN_TERMS: usize = 512;

/// Marks a wedge node whose reducer-tree parent is the origin.
const WEDGE_ROOT: u16 = u16::MAX;

/// One canonical orbit representative $\delta = a + b\omega$ of the wedge,
/// with its reducer-tree edge.
#[derive(Clone, Copy, Debug)]
struct WedgeNode {
    /// Coefficient of 1. The reducer needs only the tree shape at runtime;
    /// the coefficients define the node and anchor the first-principles
    /// re-derivations in the tests.
    #[allow(dead_code)]
    a: i16,
    /// Coefficient of $\omega$.
    #[allow(dead_code)]
    b: i16,
    /// Index of $p(\delta)$ in the wedge, or [`WEDGE_ROOT`] when the parent
    /// is the origin. Always a strictly later index: nodes are ordered by
    /// decreasing `a` and the parent map decrements `a`.
    parent: u16,
    /// Whether the parent edge subtracts $1 + \omega$ (`true`) or $1$.
    diagonal: bool,
}

/// The digit assigned to one residue class of $\mathbf{Z}[\omega]/B$: the
/// canonical representative's coefficients (for the recoding subtraction)
/// and its packed `1 + 6*orbit + unit` code (`0` for the zero class). Units
/// are ordered `[+1, -1, +ω, -ω, +ω², -ω²]` as in the parent module, so
/// `unit >> 1` is the x-rotation exponent and `unit & 1` the y negation.
#[derive(Clone, Copy, Debug)]
struct ResidueDigit {
    da: i8,
    db: i8,
    code: u16,
}

/// The per-width tables of the orbit backend: the canonical wedge with its
/// reducer tree, and the $B^2$-entry residue-to-digit table. Construction
/// re-derives and asserts the unit-orbit tiling, so a wrong table cannot be
/// built. Rebuilt per MSM (microseconds; the MSMs this backend serves cost
/// milliseconds).
#[derive(Debug)]
pub(super) struct OrbitParams {
    /// The window width $c$ (radix $B = 2^c$).
    window_bits: usize,
    /// Exact upper bound on recoded windows, from [`window_count`].
    window_count: usize,
    /// Wedge nodes ordered by strictly decreasing `a` (children precede
    /// parents).
    wedge: Vec<WedgeNode>,
    /// Digit table indexed by `(a mod B) << c | (b mod B)`.
    residues: Vec<ResidueDigit>,
}

/// Multiplies $a + b\omega$ by the unit with the given code-order index
/// (see [`ResidueDigit`]); $\omega(a + b\omega) = -b + (a - b)\omega$.
fn unit_times(unit: usize, mut a: i32, mut b: i32) -> (i32, i32) {
    for _ in 0..(unit >> 1) {
        let (ra, rb) = (-b, a - b);
        a = ra;
        b = rb;
    }
    if unit & 1 == 1 {
        a = -a;
        b = -b;
    }
    (a, b)
}

/// The exact maximum number of radix-$2^c$ digit positions needed to recode
/// a GLV half pair. Digit coefficients are bounded by
/// $D = \lfloor(2B - 1)/3\rfloor$ (the wedge maximizes its `a` coordinate at
/// $\lfloor(2B-1)/3\rfloor$, and unit rotations of $a + b\omega$ have
/// coefficients in $\pm\{a, b, a - b\}$), so coefficient magnitudes obey
/// $|a'| \le \lfloor(|a| + D)/B\rfloor$; iterating that from the component
/// bound $2^{127} - 1$ until zero counts the positions. The bound is tight
/// (the `window_count_is_exact` test exhibits inputs that attain it).
pub(super) const fn window_count(window_bits: usize) -> usize {
    let d_max = ((2u128 << window_bits) - 1) / 3;
    let mut magnitude = (1u128 << GLV_COMPONENT_BITS) - 1;
    let mut count = 0;
    while magnitude > 0 {
        magnitude = (magnitude + d_max) >> window_bits;
        count += 1;
    }
    count
}

impl OrbitParams {
    pub(super) fn new(window_bits: usize) -> Self {
        assert!((MIN_WINDOW_BITS..=MAX_WINDOW_BITS).contains(&window_bits));
        let radix = 1i32 << window_bits;

        // The wedge, ordered by decreasing `a` so that children (which have
        // strictly larger `a`) precede their parents.
        let mut coeffs = Vec::new();
        for a in (1..radix).rev() {
            for b in 0..a {
                if 2 * a - b <= radix && a + b < radix {
                    coeffs.push((a, b));
                }
            }
        }
        debug_assert_eq!(coeffs.len(), ((radix * radix + 2) / 6) as usize);

        let mut index = alloc::vec![WEDGE_ROOT; (radix * radix) as usize];
        for (i, &(a, b)) in coeffs.iter().enumerate() {
            index[((a << window_bits) | b) as usize] = u16::try_from(i).expect("wedge fits u16");
        }
        let wedge: Vec<WedgeNode> = coeffs
            .iter()
            .map(|&(a, b)| {
                let diagonal = a <= 2 * b;
                let (pa, pb) = if diagonal { (a - 1, b - 1) } else { (a - 1, b) };
                let parent = if (pa, pb) == (0, 0) {
                    WEDGE_ROOT
                } else {
                    let parent = index[((pa << window_bits) | pb) as usize];
                    debug_assert_ne!(parent, WEDGE_ROOT, "parent must stay in the wedge");
                    parent
                };
                WedgeNode {
                    a: a as i16,
                    b: b as i16,
                    parent,
                    diagonal,
                }
            })
            .collect();

        // The residue-to-digit table: place every unit rotation of every
        // orbit representative. A residue hit twice must be one of the three
        // 2-torsion classes, where `u` and `-u` produce the same residue;
        // both factorizations share the wedge node, so first-write-wins is
        // consistent.
        let mut residues = alloc::vec![
            ResidueDigit {
                da: 0,
                db: 0,
                code: 0
            };
            (radix * radix) as usize
        ];
        for (orbit, &(a, b)) in coeffs.iter().enumerate() {
            for unit in 0..6 {
                let (da, db) = unit_times(unit, a, b);
                let slot = &mut residues
                    [((da.rem_euclid(radix) << window_bits) | db.rem_euclid(radix)) as usize];
                if slot.code == 0 {
                    *slot = ResidueDigit {
                        da: i8::try_from(da).expect("digit coefficient fits i8"),
                        db: i8::try_from(db).expect("digit coefficient fits i8"),
                        code: u16::try_from(1 + orbit * 6 + unit).expect("digit code fits u16"),
                    };
                } else {
                    debug_assert_eq!(
                        usize::from(slot.code - 1) / 6,
                        orbit,
                        "colliding residues must share a bucket"
                    );
                }
            }
        }
        // Exact tiling: the zero class and only the zero class has no digit.
        // This holds by the orbit count (Burnside) and is re-checked here so
        // a wrong wedge cannot mis-multiply.
        assert!(
            residues
                .iter()
                .enumerate()
                .all(|(i, digit)| (digit.code == 0) == (i == 0)),
            "unit orbits of the wedge must tile the nonzero residues mod {radix}"
        );

        OrbitParams {
            window_bits,
            window_count: window_count(window_bits),
            wedge,
            residues,
        }
    }

    /// The number of buckets per window, $(B^2 + 2)/6$.
    fn bucket_count(&self) -> usize {
        self.wedge.len()
    }

    /// The exact recoding window bound for this width (the required row
    /// stride of every digit matrix fed to [`windows_sum`]).
    pub(super) fn window_stride(&self) -> usize {
        self.window_count
    }

    /// The window width $c$ these parameters were built for.
    #[cfg(feature = "multicore")]
    pub(super) fn width(&self) -> usize {
        self.window_bits
    }
}

/// One base point's digit-ready coordinates: the three $\zeta$-rotations of
/// x (one field multiplication; $\zeta^2 x = -x - \zeta x$) and y. A digit's
/// unit picks `xs[e]` and a y sign, so bucket filling never multiplies.
/// (Also the tail-MSM base representation of the prepared zero-check in
/// [`super::zero`], which is why the fields are visible to the parent.)
#[derive(Clone, Copy)]
pub(super) struct RotatedBase<F> {
    pub(super) xs: [F; 3],
    pub(super) y: F,
}

#[cfg(feature = "orbits")]
pub(super) fn rotate_base<C: GlvParams>(base: &C::AffineExt) -> RotatedBase<C::Base> {
    let (x, y) = C::affine_xy(base);
    let xz = x * <C::Base as ff::WithSmallOrderMulGroup<3>>::ZETA;
    RotatedBase {
        xs: [x, xz, -x - xz],
        y,
    }
}

#[cfg(feature = "orbits")]
fn rotated_bases<C: GlvParams>(
    bases: &[C::AffineExt],
    num_threads: usize,
) -> Vec<RotatedBase<C::Base>> {
    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    #[cfg(feature = "multicore")]
    if num_threads > 1 {
        return bases.par_iter().map(rotate_base::<C>).collect();
    }
    bases.iter().map(rotate_base::<C>).collect()
}

/// Recodes one component pair into `row` (which the caller zeroed), lowest
/// window first, returning the number of digit positions used (the last
/// used position always holds a nonzero digit: a zero digit means the value
/// was a nonzero multiple of the radix, so the quotient is nonzero and the
/// recoding continues). See the module docs for the exactness and overflow
/// arguments; the row length is [`OrbitParams::window_count`], which the
/// descent bound proves sufficient for any in-range pair.
pub(super) fn recode_row(
    params: &OrbitParams,
    first: SignedMagnitude,
    second: SignedMagnitude,
    row: &mut [u16],
) -> usize {
    let signed = |component: SignedMagnitude| {
        debug_assert_eq!(component.magnitude >> GLV_COMPONENT_BITS, 0);
        if component.negative {
            -(component.magnitude as i128)
        } else {
            component.magnitude as i128
        }
    };
    let mut a = signed(first);
    let mut b = signed(second);
    let mask = (1i128 << params.window_bits) - 1;
    for (position, slot) in row.iter_mut().enumerate() {
        if a == 0 && b == 0 {
            return position;
        }
        let digit = params.residues[(((a & mask) << params.window_bits) | (b & mask)) as usize];
        *slot = digit.code;
        a = (a >> params.window_bits) + i128::from(digit.da < 0);
        b = (b >> params.window_bits) + i128::from(digit.db < 0);
    }
    debug_assert!(a == 0 && b == 0, "recoding must fit the window bound");
    row.len()
}

/// The scalar-major digit matrix and the number of windows actually in use
/// (one past the highest nonzero digit of any scalar). Rows keep the full
/// [`OrbitParams::window_count`] stride; rows of identity bases are left
/// zero so the window fills never test bases again. Small-magnitude
/// workloads recode to far fewer active windows than the bound, and the
/// drivers walk only those.
#[cfg(feature = "orbits")]
fn digit_matrix<C: GlvParams>(
    params: &OrbitParams,
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[C::AffineExt],
    num_threads: usize,
) -> (Vec<u16>, usize) {
    let width = params.window_count;
    let mut digits = alloc::vec![0u16; components.len() * width];
    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    #[cfg(feature = "multicore")]
    if num_threads > 1 {
        let active = digits
            .par_chunks_mut(width)
            .zip(components.par_iter().zip(bases.par_iter()))
            .map(|(row, (&(first, second), base))| {
                if bool::from(base.is_identity()) {
                    0
                } else {
                    recode_row(params, first, second, row)
                }
            })
            .max()
            .unwrap_or(0);
        return (digits, active);
    }
    let mut active = 0;
    for (row, (&(first, second), base)) in digits
        .chunks_exact_mut(width)
        .zip(components.iter().zip(bases))
    {
        if !bool::from(base.is_identity()) {
            active = active.max(recode_row(params, first, second, row));
        }
    }
    (digits, active)
}

/// Stages one window's bucket contents: counts per orbit, then scatters
/// each nonzero digit's unit-rotated point into its orbit's range.
fn window_points<F: Field>(
    params: &OrbitParams,
    digits: &[u16],
    window: usize,
    rotated: &[RotatedBase<F>],
) -> (Vec<AffinePoint<F>>, Vec<usize>) {
    let width = params.window_count;
    let mut counts = alloc::vec![0usize; params.bucket_count()];
    for row in digits.chunks_exact(width) {
        let code = row[window];
        if code != 0 {
            counts[usize::from(code - 1) / 6] += 1;
        }
    }

    let mut offsets = Vec::with_capacity(counts.len() + 1);
    offsets.push(0);
    for count in counts {
        offsets.push(offsets.last().copied().unwrap() + count);
    }

    let mut positions = offsets[..offsets.len() - 1].to_vec();
    let mut points = alloc::vec![
        AffinePoint {
            x: F::ZERO,
            y: F::ZERO,
        };
        *offsets.last().unwrap()
    ];
    for (row, base) in digits.chunks_exact(width).zip(rotated) {
        let code = usize::from(row[window]);
        if code == 0 {
            continue;
        }
        let (orbit, unit) = ((code - 1) / 6, (code - 1) % 6);
        let position = positions[orbit];
        points[position] = AffinePoint {
            x: base.xs[unit >> 1],
            y: if unit & 1 == 1 { -base.y } else { base.y },
        };
        positions[orbit] = position + 1;
    }

    (points, offsets)
}

/// The hexagonal weighted-bucket reducer: $\sum_\delta [\delta]Q_\delta$ in
/// $2m - 2$ projective additions plus one endomorphism application, via
/// children-first subtree accumulation and $A - \phi^2(H)$ (see the module
/// docs). Empty buckets ride along as identities.
fn reduce_hex_weighted<C: GlvParams>(
    params: &OrbitParams,
    buckets: &[Option<AffinePoint<C::Base>>],
) -> C {
    debug_assert_eq!(buckets.len(), params.wedge.len());
    let mut subtree: Vec<C> = buckets
        .iter()
        .map(|bucket| match bucket {
            Some(point) => C::from(C::affine_unchecked(
                point.x,
                point.y,
                private::CrateToken(()),
            )),
            None => C::identity(),
        })
        .collect();

    let mut axial = C::identity();
    let mut diagonal = C::identity();
    for k in 0..subtree.len() {
        // Nodes are ordered children-first, so `subtree[k]` is complete.
        let sum = subtree[k];
        let node = params.wedge[k];
        if node.diagonal {
            diagonal += sum;
        } else {
            axial += sum;
        }
        if node.parent != WEDGE_ROOT {
            subtree[usize::from(node.parent)] += sum;
        }
    }
    axial - diagonal.endo().endo()
}

/// $\sum_{j \in \text{range}} B^{j - \text{range.start}} C_j$ by Horner over
/// the range's windows, staging and reducing one window at a time through
/// the parent module's fused batched-affine reduction.
pub(super) fn windows_sum<C: GlvParams>(
    params: &OrbitParams,
    digits: &[u16],
    rotated: &[RotatedBase<C::Base>],
    range: core::ops::Range<usize>,
) -> Option<C> {
    let mut acc = C::identity();
    for window in range.clone().rev() {
        if window + 1 != range.end {
            for _ in 0..params.window_bits {
                acc = acc.double();
            }
        }
        let (points, offsets) = window_points(params, digits, window, rotated);
        let buckets = reduce_affine_buckets(points, offsets)?;
        acc += reduce_hex_weighted::<C>(params, &buckets);
    }
    Some(acc)
}

/// The orbit-backend MSM over decomposed components. Callers guarantee the
/// components respect the [`GLV_COMPONENT_BITS`] bound (as
/// [`super::checked_signed_magnitudes`] enforces). Parallel runs schedule
/// the windows through the shared balanced reduction tree
/// ([`super::balanced_windows_sum`]).
#[cfg(feature = "orbits")]
pub(super) fn multiexp<C: GlvParams>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[C::AffineExt],
    window_bits: usize,
    num_threads: usize,
) -> Option<C> {
    debug_assert_eq!(components.len(), bases.len());
    let params = OrbitParams::new(window_bits);
    let rotated = rotated_bases::<C>(bases, num_threads);
    // Walk only the windows some scalar reaches: small-magnitude workloads
    // recode far below the full-width bound.
    let (digits, active_windows) = digit_matrix::<C>(&params, components, bases, num_threads);

    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    #[cfg(feature = "multicore")]
    if num_threads > 1 {
        return super::balanced_windows_sum::<C>(active_windows, window_bits, |window| {
            windows_sum::<C>(&params, &digits, &rotated, window..window + 1)
        });
    }
    windows_sum::<C>(&params, &digits, &rotated, 0..active_windows)
}

/// Test convenience: the work component of [`estimated_costs`].
#[cfg(all(test, feature = "orbits"))]
pub(super) fn estimated_work(
    profile: &MagnitudeProfile,
    window_bits: usize,
    num_threads: usize,
) -> Option<usize> {
    estimated_costs(profile, window_bits, num_threads).map(|(work, _)| work)
}

/// Estimates the orbit backend's costs for a profiled input as a
/// `(work, traffic)` pair: the dominant group work, in units comparable to
/// [`super::estimated_signed_booth_costs`]'s, and the estimate's total
/// group-operation count (visits and weighted-bucket additions), which the
/// planner's shared-bandwidth floor scales — total traffic is what a wide
/// pool cannot divide away (see `plan_multiexp`).
///
/// The work model carries two calibration constants fit to the
/// `msm_backend_timings` harness against the Booth backend on 32-core
/// x86-64 (portable field backend) — the unique pair (over
/// eighths/sixteenths/thirty-seconds of a visit) that reproduces every
/// measured serial backend-and-width preference from 512 to 65,536 terms
/// and flips no parallel cell against its measured winner:
///
/// - A point/window **visit** is priced at 27/32 of a Booth visit. Both are
///   one batched-affine bucket addition, but an orbit window makes a single
///   pass over one digit row and one rotation table where a Booth window
///   walks two component streams into 3–6x as many bucket slots. (Booth's
///   model, being the older pinned contract, is left untouched.)
/// - A **weighted-bucket addition** (the hexagonal reducer's $2m - 2$
///   projective additions) is priced at 3/2 visits — a full Jacobian
///   addition against the fill's batched affine additions — so a window's
///   weighted reduction costs $3(m - 1)$ units.
///
/// A scalar visits window `j` only if its joint magnitude reaches past
/// `j * c` bits, and the drivers walk (and weighted-reduce, and
/// Horner-shift) only the windows some scalar reaches, so both terms come
/// from the profile's live counts, plus one window of recoding-carry slack.
/// This matters: radix-$2^c$ joint recoding spreads a small magnitude over
/// ~$2c/w$ as many windows as $w$-bit Booth halves, so sparse workloads
/// (like halo2 witness commitments) reprice substantially.
///
/// The parallel estimate prices [`multiexp_parallel`]'s per-window tasks as
/// the larger of perfectly-balanced total work and the critical worker
/// (its $\lceil W/\text{workers}\rceil$ windows plus the top window's shift
/// doublings) — work stealing achieves the former at low worker counts;
/// the latter binds when workers exceed half the window count.
#[cfg(feature = "orbits")]
pub(super) fn estimated_costs(
    profile: &MagnitudeProfile,
    window_bits: usize,
    num_threads: usize,
) -> Option<(usize, usize)> {
    if !(PLAN_MIN_WINDOW_BITS..=MAX_WINDOW_BITS).contains(&window_bits)
        || profile.terms < PLAN_MIN_TERMS
    {
        return None;
    }
    let window_count = window_count(window_bits);
    let buckets = (1usize.checked_shl(u32::try_from(2 * window_bits).ok()?)? + 2) / 6;

    let mut raw_visits = 0usize;
    let mut active_windows = 0usize;
    for window in 0..window_count {
        let live = profile.scalar_live(window.checked_mul(window_bits)?);
        if live > 0 {
            raw_visits = raw_visits.checked_add(live)?;
            active_windows = window + 1;
        }
    }
    if active_windows == 0 {
        // Every scalar is zero (or every base the identity).
        return Some((0, 0));
    }
    // The recoding can carry one window past the top magnitude.
    let active_windows = (active_windows + 1).min(window_count);
    let visits = raw_visits.checked_mul(27)? / 32;
    let bucket_additions = buckets
        .checked_sub(1)?
        .checked_mul(3)?
        .checked_mul(active_windows)?;
    let doublings = window_bits.checked_mul(active_windows - 1)?;
    let traffic = visits.checked_add(bucket_additions)?;

    if num_threads <= 1 {
        return Some((traffic.checked_add(doublings)?, traffic));
    }

    let workers = num_threads.min(active_windows);
    // All shift doublings, spread across workers in the balanced term:
    // window j pays j * window_bits.
    let shifts = window_bits.checked_mul(active_windows * (active_windows - 1) / 2)?;
    let balanced = visits
        .checked_add(bucket_additions)?
        .checked_add(shifts)?
        .div_ceil(workers);
    // Task-count quantization: a worker must complete whole windows, priced
    // at the average window (work stealing spreads the dense low windows,
    // so the average — not the peak — is what a critical worker sees; on a
    // uniform full-width profile the two coincide).
    let quantized = visits
        .checked_add(bucket_additions)?
        .div_ceil(active_windows)
        .checked_mul(active_windows.div_ceil(workers))?
        .checked_add(doublings)?;
    Some((balanced.max(quantized), traffic))
}

#[cfg(all(test, feature = "orbits"))]
mod tests {
    use super::super::{GlvParams, decompose, digit_scalar, testutil};
    use super::*;
    use crate::arithmetic::CurveExt;
    use crate::{pallas, vesta};
    use ff::{PrimeField, WithSmallOrderMulGroup};

    /// Eisenstein multiplication on coefficient pairs:
    /// $(a + b\omega)(c + d\omega) = (ac - bd) + (ad + bc - bd)\omega$.
    fn emul(x: (i32, i32), y: (i32, i32)) -> (i32, i32) {
        (x.0 * y.0 - x.1 * y.1, x.0 * y.1 + x.1 * y.0 - x.1 * y.1)
    }

    /// The units in code order `[+1, -1, +ω, -ω, +ω², -ω²]` (ω² = -1 - ω).
    const UNITS: [(i32, i32); 6] = [(1, 0), (-1, 0), (0, 1), (0, -1), (-1, -1), (1, 1)];

    /// The value of a digit code as an Eisenstein coefficient pair.
    fn code_coeffs(params: &OrbitParams, code: u16) -> (i32, i32) {
        assert_ne!(code, 0);
        let (orbit, unit) = (usize::from(code - 1) / 6, usize::from(code - 1) % 6);
        let node = params.wedge[orbit];
        emul(UNITS[unit], (i32::from(node.a), i32::from(node.b)))
    }

    #[test]
    fn wedge_construction_first_principles() {
        for window_bits in MIN_WINDOW_BITS..=MAX_WINDOW_BITS {
            let params = OrbitParams::new(window_bits);
            let radix = 1i32 << window_bits;
            let coeff_bound = (2 * radix - 1) / 3;

            // Bucket count and wedge membership.
            assert_eq!(params.bucket_count() as i32, (radix * radix + 2) / 6);
            for (k, node) in params.wedge.iter().enumerate() {
                let (a, b) = (i32::from(node.a), i32::from(node.b));
                assert!(a > b && b >= 0 && 2 * a - b <= radix && a + b < radix);
                assert!(a <= coeff_bound);
                // Parent map and label, re-derived.
                let (pa, pb) = if a > 2 * b {
                    (a - 1, b)
                } else {
                    (a - 1, b - 1)
                };
                assert_eq!(node.diagonal, a <= 2 * b);
                if (pa, pb) == (0, 0) {
                    assert_eq!(node.parent, WEDGE_ROOT);
                } else {
                    let parent = &params.wedge[usize::from(node.parent)];
                    assert_eq!((i32::from(parent.a), i32::from(parent.b)), (pa, pb));
                    assert!(
                        usize::from(node.parent) > k,
                        "children must precede parents"
                    );
                    let step = if node.diagonal { (1, 1) } else { (1, 0) };
                    assert_eq!((a - pa, b - pb), step);
                }
            }
            assert_eq!(
                params
                    .wedge
                    .iter()
                    .filter(|n| n.parent == WEDGE_ROOT)
                    .count(),
                1,
                "the wedge tree has one root"
            );

            // The residue table: zero class only at index zero, and every
            // entry is the correctly factored canonical digit of its class.
            for (index, digit) in params.residues.iter().enumerate() {
                let (ra, rb) = (
                    (index >> window_bits) as i32,
                    (index & (radix as usize - 1)) as i32,
                );
                if index == 0 {
                    assert_eq!(digit.code, 0);
                    continue;
                }
                assert_ne!(digit.code, 0, "class ({ra}, {rb}) must have a digit");
                let (da, db) = (i32::from(digit.da), i32::from(digit.db));
                assert_eq!(code_coeffs(&params, digit.code), (da, db));
                assert_eq!((da.rem_euclid(radix), db.rem_euclid(radix)), (ra, rb));
                assert!(da.abs() <= coeff_bound && db.abs() <= coeff_bound);
            }
        }
    }

    #[test]
    fn window_count_is_exact() {
        assert_eq!(window_count(3), 43);
        assert_eq!(window_count(4), 33);
        assert_eq!(window_count(5), 26);
        assert_eq!(window_count(6), 22);

        for window_bits in MIN_WINDOW_BITS..=MAX_WINDOW_BITS {
            let params = OrbitParams::new(window_bits);
            // Exhaustive termination and closure over the tail box
            // |a|, |b| <= 8 (recoded magnitudes contract into it and cannot
            // leave it: (8 + D)/B < 8 for every supported width), plus the
            // extremal component pairs, which must attain the bound.
            use std::collections::BTreeMap;
            fn tail(
                params: &OrbitParams,
                a: i128,
                b: i128,
                memo: &mut BTreeMap<(i128, i128), Option<usize>>,
            ) -> usize {
                if a == 0 && b == 0 {
                    return 0;
                }
                match memo.get(&(a, b)) {
                    Some(Some(t)) => return *t,
                    Some(None) => panic!("recoding cycle at ({a}, {b})"),
                    None => {}
                }
                memo.insert((a, b), None);
                let mask = (1i128 << params.window_bits) - 1;
                let digit =
                    params.residues[(((a & mask) << params.window_bits) | (b & mask)) as usize];
                let na = (a >> params.window_bits) + i128::from(digit.da < 0);
                let nb = (b >> params.window_bits) + i128::from(digit.db < 0);
                assert!(na.abs() <= 8 && nb.abs() <= 8, "recoding escaped the box");
                let t = 1 + tail(params, na, nb, memo);
                memo.insert((a, b), Some(t));
                t
            }
            let mut memo = BTreeMap::new();
            for a in -8..=8 {
                for b in -8..=8 {
                    tail(&params, a, b, &mut memo);
                }
            }

            let max = (1u128 << GLV_COMPONENT_BITS) - 1;
            let mut worst = 0;
            for (first, second) in [(max, max), (max, 0), (0, max), (max, 1), (max - 1, max)] {
                for signs in 0..4 {
                    let mut row = alloc::vec![0u16; params.window_count + 8];
                    recode_row(
                        &params,
                        SignedMagnitude {
                            negative: signs & 1 == 1,
                            magnitude: first,
                        },
                        SignedMagnitude {
                            negative: signs & 2 == 2,
                            magnitude: second,
                        },
                        &mut row,
                    );
                    let used = row
                        .iter()
                        .rposition(|&code| code != 0)
                        .map_or(0, |top| top + 1);
                    worst = worst.max(used);
                }
            }
            assert!(worst <= params.window_count);
            assert_eq!(
                worst, params.window_count,
                "the window bound must be attained at width {window_bits}"
            );
        }
    }

    /// The digits of a recoded scalar fold back to the scalar in the field:
    /// radix-B Horner with each digit mapped through ω → λ.
    fn recoding_reconstructs<C: GlvParams>() {
        for window_bits in MIN_WINDOW_BITS..=MAX_WINDOW_BITS {
            let params = OrbitParams::new(window_bits);
            let radix = C::ScalarExt::from(1u64 << window_bits);
            let check = |k: C::ScalarExt| {
                let (first, second) = decompose::<C>(&k);
                let mut row = alloc::vec![0u16; params.window_count];
                recode_row(&params, first.into(), second.into(), &mut row);
                let mut acc = C::ScalarExt::ZERO;
                for &code in row.iter().rev() {
                    acc *= radix;
                    if code != 0 {
                        let (da, db) = code_coeffs(&params, code);
                        let signed = |v: i32| {
                            let m = C::ScalarExt::from(u64::from(v.unsigned_abs()));
                            if v < 0 { -m } else { m }
                        };
                        acc += signed(da) + signed(db) * C::ScalarExt::ZETA;
                    }
                }
                assert_eq!(acc, k, "digits must reconstruct k at width {window_bits}");
            };
            check(C::ScalarExt::ZERO);
            check(C::ScalarExt::ONE);
            check(-C::ScalarExt::ONE);
            check(C::ScalarExt::ZETA);
            check(-C::ScalarExt::ZETA);
            check(C::ScalarExt::ZETA + C::ScalarExt::ONE);
            for k in testutil::scalars::<C::ScalarExt>(200) {
                check(k);
            }
        }
    }

    /// The hexagonal reducer matches the naive weighted sum
    /// $\sum_\delta [a_\delta + b_\delta\lambda] Q_\delta$ computed with
    /// native scalar multiplications, across bucket occupancy patterns.
    fn hex_reducer_matches_naive<C: GlvParams>() {
        let generator = C::generator();
        for window_bits in [3, 5] {
            let params = OrbitParams::new(window_bits);
            let m = params.bucket_count();
            for pattern in 0..4u64 {
                let buckets: Vec<Option<AffinePoint<C::Base>>> = (0..m)
                    .map(|k| {
                        // Patterns: dense, half-empty, sparse, singleton.
                        let keep = match pattern {
                            0 => true,
                            1 => k % 2 == 0,
                            2 => k % 7 == 3,
                            _ => k == m / 2,
                        };
                        keep.then(|| {
                            let point = generator
                                * (C::ScalarExt::from(k as u64 + 1).square()
                                    + C::ScalarExt::from(pattern + 1));
                            let affine = C::AffineExt::from(point);
                            let (x, y) = C::affine_xy(&affine);
                            AffinePoint { x, y }
                        })
                    })
                    .collect();

                let mut expected = C::identity();
                for (node, bucket) in params.wedge.iter().zip(&buckets) {
                    if let Some(point) = bucket {
                        let weight = {
                            let signed = |v: i16| {
                                let m = C::ScalarExt::from(u64::from(v.unsigned_abs()));
                                if v < 0 { -m } else { m }
                            };
                            signed(node.a) + signed(node.b) * C::ScalarExt::ZETA
                        };
                        expected += C::from(C::affine_unchecked(
                            point.x,
                            point.y,
                            private::CrateToken(()),
                        )) * weight;
                    }
                }
                assert_eq!(
                    reduce_hex_weighted::<C>(&params, &buckets),
                    expected,
                    "hex reducer mismatch at width {window_bits}, pattern {pattern}"
                );
            }
        }
    }

    /// The full orbit MSM against known-answer inputs (with identity,
    /// duplicate, and inverse bases and edge-case scalars) at every
    /// supported width.
    fn orbit_multiexp_matches_expected<C: GlvParams>(num_threads: usize) {
        for window_bits in MIN_WINDOW_BITS..=MAX_WINDOW_BITS {
            for terms in [513, 2_048] {
                let (scalars, bases, expected) = testutil::verifier_multiexp_inputs::<C>(terms);
                let components = scalars
                    .iter()
                    .map(decompose::<C>)
                    .map(super::super::checked_signed_magnitudes)
                    .collect::<Option<Vec<_>>>()
                    .expect("decompositions fit the component bound");
                let actual = multiexp::<C>(&components, &bases, window_bits, num_threads)
                    .expect("valid points have invertible denominators");
                assert_eq!(
                    actual, expected,
                    "orbit MSM mismatch at width {window_bits}, {terms} terms, \
                     {num_threads} threads"
                );
            }
        }
    }

    /// Digit scalars agree between the joint-NAF table and the orbit table
    /// on the codes they share (both use `1 + 6*orbit + unit` packing, so
    /// this pins the unit ordering convention to the parent module's).
    fn unit_convention_matches_parent<C: GlvParams>() {
        let params = OrbitParams::new(3);
        // The wedge contains (1, 0) = Δ0 (as its root, the last node); its
        // six unit codes must produce the same digit values as the parent
        // module's codes 1..=6 (Δ0's units), pinning the shared
        // `[+1, -1, +ω, -ω, +ω², -ω²]` ordering.
        let root = params.wedge.len() - 1;
        assert_eq!(
            (params.wedge[root].a, params.wedge[root].b),
            (1, 0),
            "the wedge root must be Δ0",
        );
        for unit in 0..6u16 {
            let (da, db) = code_coeffs(&params, 1 + root as u16 * 6 + unit);
            let expected = digit_scalar::<C::ScalarExt>(1 + unit as u8);
            let signed = |v: i32| {
                let m = C::ScalarExt::from(u64::from(v.unsigned_abs()));
                if v < 0 { -m } else { m }
            };
            assert_eq!(signed(da) + signed(db) * C::ScalarExt::ZETA, expected);
        }
    }

    macro_rules! orbit_tests {
        ($mod_name:ident, $curve:ty) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn recoding() {
                    recoding_reconstructs::<$curve>();
                }
                #[test]
                fn hex_reducer() {
                    hex_reducer_matches_naive::<$curve>();
                }
                #[test]
                fn multiexp_serial_widths() {
                    orbit_multiexp_matches_expected::<$curve>(1);
                }
                #[cfg(feature = "multicore")]
                #[test]
                fn multiexp_parallel_widths() {
                    for num_threads in [2, 3, 8] {
                        maybe_rayon::ThreadPoolBuilder::new()
                            .num_threads(num_threads)
                            .build()
                            .expect("test thread pool must build")
                            .install(|| orbit_multiexp_matches_expected::<$curve>(num_threads));
                    }
                }
                #[test]
                fn unit_convention() {
                    unit_convention_matches_parent::<$curve>();
                }
            }
        };
    }

    orbit_tests!(pallas_orbit, pallas::Point);
    orbit_tests!(vesta_orbit, vesta::Point);

    /// Property-based recoding checks, mirroring the parent module's
    /// strategy: whole-field scalars through `from_uniform_bytes`.
    mod pbt {
        use proptest::prelude::*;

        use super::*;

        fn scalar_strategy<F: PrimeField + ff::FromUniformBytes<64>>() -> impl Strategy<Value = F> {
            proptest::array::uniform4(any::<u64>()).prop_map(|limbs| {
                let mut bytes = [0u8; 64];
                for (i, l) in limbs.iter().enumerate() {
                    bytes[i * 8..(i + 1) * 8].copy_from_slice(&l.to_le_bytes());
                }
                F::from_uniform_bytes(&bytes)
            })
        }

        macro_rules! orbit_pbt {
            ($mod_name:ident, $curve:ty) => {
                mod $mod_name {
                    use super::*;

                    type Scalar = <$curve as CurveExt>::ScalarExt;

                    proptest! {
                        /// For all k and widths: the orbit digits fold back
                        /// to k under ω → λ radix-B Horner.
                        #[test]
                        fn orbit_recoding_reconstructs(k in scalar_strategy::<Scalar>()) {
                            for window_bits in MIN_WINDOW_BITS..=MAX_WINDOW_BITS {
                                let params = OrbitParams::new(window_bits);
                                let radix = Scalar::from(1u64 << window_bits);
                                let (first, second) = decompose::<$curve>(&k);
                                let mut row = alloc::vec![0u16; params.window_count];
                                recode_row(&params, first.into(), second.into(), &mut row);
                                let mut acc = Scalar::ZERO;
                                for &code in row.iter().rev() {
                                    acc *= radix;
                                    if code != 0 {
                                        let (da, db) = code_coeffs(&params, code);
                                        let signed = |v: i32| {
                                            let m = Scalar::from(u64::from(v.unsigned_abs()));
                                            if v < 0 { -m } else { m }
                                        };
                                        acc += signed(da) + signed(db) * Scalar::ZETA;
                                    }
                                }
                                prop_assert_eq!(acc, k);
                            }
                        }
                    }
                }
            };
        }

        orbit_pbt!(pallas_pbt, pallas::Point);
        orbit_pbt!(vesta_pbt, vesta::Point);
    }

    /// Wedge nodes of width 3 against the module docs' worked example.
    #[test]
    fn width_3_wedge_matches_worked_example() {
        let params = OrbitParams::new(3);
        let coeffs: Vec<(i16, i16)> = params.wedge.iter().map(|n| (n.a, n.b)).collect();
        // Decreasing a; children before parents.
        assert_eq!(
            coeffs,
            [
                (5, 2),
                (4, 0),
                (4, 1),
                (4, 2),
                (4, 3),
                (3, 0),
                (3, 1),
                (3, 2),
                (2, 0),
                (2, 1),
                (1, 0)
            ]
        );
    }

    /// A profile whose every scalar has both halves at the full 127-bit
    /// magnitude: every window of every width is live.
    fn saturated_profile(terms: usize) -> MagnitudeProfile {
        let full = SignedMagnitude {
            negative: false,
            magnitude: (1u128 << (GLV_COMPONENT_BITS - 1)) + 1,
        };
        MagnitudeProfile::new(&alloc::vec![(full, full); terms])
    }

    /// A profile whose every scalar's joint magnitude is exactly `bits`.
    fn uniform_profile(terms: usize, bits: usize) -> MagnitudeProfile {
        let magnitude = if bits == 0 { 0 } else { 1u128 << (bits - 1) };
        let component = SignedMagnitude {
            negative: false,
            magnitude,
        };
        MagnitudeProfile::new(&alloc::vec![(component, component); terms])
    }

    #[test]
    fn estimated_work_model() {
        // Serial, full width: every window live, so
        // (27/32)·terms·W + 3(m - 1)·W + c(W - 1). At width 5: 44,928
        // discounted visits, 510 weighted-bucket units per window, 26
        // windows.
        let full = saturated_profile(2_048);
        assert_eq!(
            estimated_work(&full, 5, 1),
            Some(26 * 2_048 * 27 / 32 + 3 * 170 * 26 + 5 * 25)
        );
        assert_eq!(
            estimated_work(&full, 6, 1),
            Some(22 * 2_048 * 27 / 32 + 3 * 682 * 22 + 6 * 21)
        );
        // Out-of-range widths are rejected, not mispriced.
        assert_eq!(estimated_work(&full, 2, 1), None);
        // Width 3 is implemented but not planned; see PLAN_MIN_WINDOW_BITS.
        assert_eq!(estimated_work(&full, 3, 1), None);
        assert_eq!(estimated_work(&full, 7, 1), None);
        // Parallel: max(balanced, critical worker). At width 5 on 8 workers
        // the critical worker binds: ceil(26/8) = 4 windows of peak density
        // (1,728 discounted visits + 510 bucket units) plus the top
        // window's 125 shift doublings.
        assert_eq!(estimated_work(&full, 5, 8), Some(2_238 * 4 + 5 * 25));
        // On 4 workers the critical worker still binds: 7 windows + shift
        // exceeds the balanced ceil((44,928 + 13,260 + 1,625)/4) = 14,954.
        assert_eq!(estimated_work(&full, 5, 4), Some(2_238 * 7 + 5 * 25));

        // Small magnitudes reach only their own windows: 32-bit scalars at
        // width 5 are live through window 6 (boundary 30), plus one carry
        // window — 8 windows of weighted reduction and Horner instead of 26.
        let small = uniform_profile(2_048, 32);
        assert_eq!(
            estimated_work(&small, 5, 1),
            Some(7 * 2_048 * 27 / 32 + 3 * 170 * 8 + 5 * 7)
        );
        // Zero scalars cost (almost) nothing.
        assert_eq!(estimated_work(&uniform_profile(2_048, 0), 5, 1), Some(0));
    }
}
