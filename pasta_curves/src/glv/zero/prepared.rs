//! The prepared variant table: one transformed point $\eta_a(P_i)$ per
//! (variant, base) pair, stored as $(x, \zeta x, y)$ so a digit's unit acts
//! by lookup — rotation $e$ selects $x$, $\zeta x$, or
//! $\zeta^2 x = -x - \zeta x$ (one addition and negation), and negation
//! flips $y$. 96 bytes per point before padding.
//!
//! Layout is variant-major (`layers[variant * terms + base]`): the builders
//! naturally produce whole layers, and the tail MSM reads the trivial
//! $\eta = 1$ layer as a contiguous base array. The handoff's compact
//! 64-byte representation and base-major layout are measured out: the
//! phase-contention probes show batched-affine reduction — not table
//! traffic — at ~3/4 of the runtime, with the small-table α6 mode
//! inflating under contention exactly as the 48 MiB modes do, so table
//! bytes are not the lever they appear to be (see the parent module's
//! "Deferred by measurement").
//!
//! # Construction
//!
//! The α-only codebooks admit a fast path: their variant lifts are exactly
//! $n$ and $n\alpha$ for odd $n < B/2$ (asserted by the codebook tests), so
//! the layers are the odd multiples $[n]P$ and $[n]\alpha(P)$ — two batched
//! affine addition chains (`cur += 2P` per step, one shared inversion per
//! step across all bases), seeded by one batched evaluation of the degree-3
//! map $\alpha$. Non-chain lifts (the β-subgroup modes) fall back to the
//! existing per-variant GLV batch ladder [`Table::mul_decomposed_batch`],
//! which is simple and correct; preparation is amortized, so it is only
//! optimized where that is free (the chains).
//!
//! All chain denominators are provably nonzero for nonidentity prime-order
//! inputs: $[k]P + [2]P$ is exceptional only if $[k \mp 2]P$ is the
//! identity (impossible for odd $k$ with $|k| + 2 \ll r$), doubling needs
//! $y \ne 0$ (no 2-torsion), and the α seed is exceptional only for
//! identity inputs (its kernel misses the rational group). Identity bases
//! are excluded from the chains and their table entries stay the all-zero
//! sentinel, which the online path never fetches (their digit rows are
//! forced to zero).

use alloc::vec::Vec;
use core::marker::PhantomData;

use ff::{Field, WithSmallOrderMulGroup};
use group::CurveAffine as _;
#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;

use super::super::{affine_ladder_safe, batch_invert_nonzero, joint_digits};
use super::super::{Decomposed, GlvParams, Table};
use super::codebook::Eis;
use super::isogeny::alpha_affine_batch;

/// One prepared point in unit-action-ready form. The identity (and every
/// never-fetched dead slot) is the all-zero value; `y = 0` cannot occur for
/// a valid point on an odd-order curve.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PreparedPoint<F> {
    pub(crate) x: F,
    pub(crate) zeta_x: F,
    pub(crate) y: F,
}

/// The affine coordinates a digit's unit selects from a prepared point:
/// $[\pm\omega^e]\,Q = (\zeta^e x, \pm y)$, with the shared unit code order
/// `[+1, -1, +ω, -ω, +ω², -ω²]`.
#[inline(always)]
pub(crate) fn unit_coords<F: Field>(point: &PreparedPoint<F>, unit: usize) -> (F, F) {
    let x = match unit >> 1 {
        0 => point.x,
        1 => point.zeta_x,
        _ => -point.x - point.zeta_x,
    };
    let y = if unit & 1 == 1 { -point.y } else { point.y };
    (x, y)
}

/// The prepared table for one codebook over one fixed base list.
#[derive(Debug)]
pub(crate) struct VariantTable<C: GlvParams> {
    layers: Vec<PreparedPoint<C::Base>>,
    terms: usize,
}

impl<C: GlvParams> VariantTable<C> {
    #[inline(always)]
    pub(crate) fn get(&self, variant: usize, base: usize) -> &PreparedPoint<C::Base> {
        &self.layers[variant * self.terms + base]
    }

    /// The prepared memory footprint in bytes.
    pub(crate) fn bytes(&self) -> usize {
        self.layers.len() * core::mem::size_of::<PreparedPoint<C::Base>>()
    }

    /// Builds the table. `live[i]` marks bases that participate (nonidentity
    /// and not merged away); dead slots stay zeroed and must never be
    /// fetched. `variants` are the codebook's exact lifts.
    pub(crate) fn build(
        bases: &[C::AffineExt],
        live: &[bool],
        variants: &[Eis],
        num_threads: usize,
    ) -> Self {
        assert_eq!(bases.len(), live.len());
        let terms = bases.len();
        let zero = PreparedPoint {
            x: C::Base::ZERO,
            zeta_x: C::Base::ZERO,
            y: C::Base::ZERO,
        };
        let mut layers = alloc::vec![zero; variants.len() * terms];

        let live_indices: Vec<usize> = (0..terms).filter(|&i| live[i]).collect();
        if live_indices.is_empty() {
            return VariantTable { layers, terms };
        }
        let live_affine: Vec<C::AffineExt> = live_indices.iter().map(|&i| bases[i]).collect();
        let (base_xs, base_ys): (Vec<C::Base>, Vec<C::Base>) =
            live_affine.iter().map(|p| C::affine_xy(p)).unzip();

        // Split the lifts into the two chain shapes and the generic rest.
        let mut p_requests: Vec<(i64, usize)> = Vec::new();
        let mut q_requests: Vec<(i64, usize)> = Vec::new();
        let mut generic: Vec<(Eis, usize)> = Vec::new();
        for (variant, &eta) in variants.iter().enumerate() {
            if eta.b == 0 && eta.a > 0 && eta.a % 2 == 1 {
                p_requests.push((eta.a, variant));
            } else if eta.b == -eta.a && eta.a > 0 && eta.a % 2 == 1 {
                q_requests.push((eta.a, variant));
            } else {
                generic.push((eta, variant));
            }
        }
        p_requests.sort_unstable();
        q_requests.sort_unstable();

        odd_multiple_layers::<C>(
            &mut layers,
            terms,
            &live_indices,
            &base_xs,
            &base_ys,
            &p_requests,
        );
        if !q_requests.is_empty() {
            let alphas = alpha_affine_batch::<C>(&live_affine);
            let (alpha_xs, alpha_ys): (Vec<C::Base>, Vec<C::Base>) =
                alphas.iter().map(|p| C::affine_xy(p)).unzip();
            odd_multiple_layers::<C>(
                &mut layers,
                terms,
                &live_indices,
                &alpha_xs,
                &alpha_ys,
                &q_requests,
            );
        }

        if !generic.is_empty() {
            let live_points: Vec<C> = live_affine.iter().map(|&p| C::from(p)).collect();
            let tables = Table::<C>::batch(&live_points);
            let table_refs: Vec<&Table<C>> = tables.iter().collect();
            let layer_for = |&(eta, _variant): &(Eis, usize)| -> Vec<C::AffineExt> {
                let decomposed = decomposed_from_pair::<C>(eta);
                let products = Table::mul_decomposed_batch(&table_refs, &decomposed);
                let mut affine = alloc::vec![C::AffineExt::identity(); products.len()];
                C::batch_normalize(&products, &mut affine);
                affine
            };
            #[cfg(not(feature = "multicore"))]
            let _ = num_threads;
            #[cfg(feature = "multicore")]
            let results: Vec<Vec<C::AffineExt>> = if num_threads > 1 {
                generic.par_iter().map(layer_for).collect()
            } else {
                generic.iter().map(layer_for).collect()
            };
            #[cfg(not(feature = "multicore"))]
            let results: Vec<Vec<C::AffineExt>> = generic.iter().map(layer_for).collect();
            for ((_, variant), affine) in generic.iter().zip(results) {
                let (xs, ys): (Vec<C::Base>, Vec<C::Base>) =
                    affine.iter().map(|p| C::affine_xy(p)).unzip();
                write_layer::<C>(&mut layers, terms, *variant, &live_indices, &xs, &ys);
            }
        }

        VariantTable { layers, terms }
    }
}

/// Recodes the small exact pair $\eta = a + b\omega$ for the GLV batch
/// ladder (which then computes $[a + b\lambda]P$ per table).
fn decomposed_from_pair<C: GlvParams>(eta: Eis) -> Decomposed<C> {
    let (digits, len) = joint_digits(i128::from(eta.a), i128::from(eta.b));
    let mut decomposed = Decomposed {
        digits,
        len,
        affine_ladder_safe: false,
        _curve: PhantomData,
    };
    decomposed.affine_ladder_safe = decomposed.len > 0 && affine_ladder_safe::<C>(&decomposed);
    decomposed
}

/// Writes one variant layer from live-ordered affine coordinates, filling
/// in the $\zeta x$ rotation (one multiplication per entry).
fn write_layer<C: GlvParams>(
    layers: &mut [PreparedPoint<C::Base>],
    terms: usize,
    variant: usize,
    live_indices: &[usize],
    xs: &[C::Base],
    ys: &[C::Base],
) {
    let zeta = <C::Base as WithSmallOrderMulGroup<3>>::ZETA;
    let layer = &mut layers[variant * terms..(variant + 1) * terms];
    for ((&index, &x), &y) in live_indices.iter().zip(xs).zip(ys) {
        layer[index] = PreparedPoint {
            x,
            zeta_x: x * zeta,
            y,
        };
    }
}

/// Batched affine doubling in place: one shared inversion of the `2y`
/// denominators. Inputs must be nonidentity points on an odd-order curve.
fn affine_double_batch<F: Field>(xs: &mut [F], ys: &mut [F]) {
    if ys.is_empty() {
        return;
    }
    let mut denominators: Vec<F> = ys.iter().map(|y| y.double()).collect();
    let mut scratch = alloc::vec![F::ZERO; denominators.len()];
    batch_invert_nonzero(&mut denominators, &mut scratch);
    for ((x, y), inverse) in xs.iter_mut().zip(ys.iter_mut()).zip(&denominators) {
        let xx = x.square();
        let slope = (xx.double() + xx) * inverse;
        let out_x = slope.square() - x.double();
        *y = slope * (*x - out_x) - *y;
        *x = out_x;
    }
}

/// Batched affine `cur += step` in place: one shared inversion of the
/// x-difference denominators, which the callers guarantee are nonzero.
fn affine_add_batch<F: Field>(xs: &mut [F], ys: &mut [F], step_xs: &[F], step_ys: &[F]) {
    if xs.is_empty() {
        return;
    }
    let mut denominators: Vec<F> = step_xs
        .iter()
        .zip(xs.iter())
        .map(|(sx, x)| *sx - *x)
        .collect();
    let mut scratch = alloc::vec![F::ZERO; denominators.len()];
    batch_invert_nonzero(&mut denominators, &mut scratch);
    for (i, inverse) in denominators.iter().enumerate() {
        let slope = (step_ys[i] - ys[i]) * inverse;
        let out_x = slope.square() - xs[i] - step_xs[i];
        ys[i] = slope * (xs[i] - out_x) - ys[i];
        xs[i] = out_x;
    }
}

/// Fills every requested odd-multiple layer `[n]S` of the seed points given
/// by `(seed_xs, seed_ys)`, walking `cur += [2]S` once and writing layers
/// as their multiples come up. `requests` is `(n, variant)` sorted by `n`.
fn odd_multiple_layers<C: GlvParams>(
    layers: &mut [PreparedPoint<C::Base>],
    terms: usize,
    live_indices: &[usize],
    seed_xs: &[C::Base],
    seed_ys: &[C::Base],
    requests: &[(i64, usize)],
) {
    let Some(&(max_n, _)) = requests.last() else {
        return;
    };
    let mut cur_xs = seed_xs.to_vec();
    let mut cur_ys = seed_ys.to_vec();
    let mut step_xs = Vec::new();
    let mut step_ys = Vec::new();
    if max_n > 1 {
        step_xs = seed_xs.to_vec();
        step_ys = seed_ys.to_vec();
        affine_double_batch(&mut step_xs, &mut step_ys);
    }
    let mut requests = requests.iter().peekable();
    let mut multiple = 1i64;
    loop {
        while let Some(&&(n, variant)) = requests.peek() {
            if n != multiple {
                break;
            }
            write_layer::<C>(layers, terms, variant, live_indices, &cur_xs, &cur_ys);
            requests.next();
        }
        if requests.peek().is_none() {
            return;
        }
        affine_add_batch(&mut cur_xs, &mut cur_ys, &step_xs, &step_ys);
        multiple += 2;
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::testutil;
    use super::super::codebook::{Codebook, CodebookMode};
    use super::*;
    use crate::{pallas, vesta};

    /// Bases with identity, duplicate, and negated entries.
    fn test_bases<C: GlvParams>(count: usize) -> Vec<C::AffineExt> {
        let generator = C::generator();
        let mut bases: Vec<C::AffineExt> = testutil::scalars::<C::ScalarExt>(count as u64)
            .map(|k| (generator * k).to_affine())
            .collect();
        bases[0] = C::AffineExt::identity();
        bases[1] = generator.to_affine();
        bases[2] = generator.to_affine();
        bases[3] = (-generator).to_affine();
        bases
    }

    /// Every table entry is $[\eta_a]P_i = [a + b\lambda]P_i$, its stored
    /// rotation is $\zeta x$, and every unit selection matches the native
    /// group operation (§23.2).
    fn table_matches_native<C: GlvParams>() {
        for mode in [
            CodebookMode::alpha_only(5),
            // β² at width 5 exercises the generic (non-chain) builder.
            CodebookMode::Subgroup {
                window_bits: 5,
                beta_power: Some(2),
            },
        ] {
            let codebook = Codebook::new(mode);
            let bases = test_bases::<C>(40);
            let live: Vec<bool> = bases.iter().map(|p| !bool::from(p.is_identity())).collect();
            let table = VariantTable::<C>::build(&bases, &live, codebook.variants(), 1);
            let lambda = <C::ScalarExt as WithSmallOrderMulGroup<3>>::ZETA;
            let zeta = <C::Base as WithSmallOrderMulGroup<3>>::ZETA;
            let signed = |v: i64| {
                let m = C::ScalarExt::from(v.unsigned_abs());
                if v < 0 {
                    -m
                } else {
                    m
                }
            };
            for (variant, &eta) in codebook.variants().iter().enumerate() {
                let mu = signed(eta.a) + signed(eta.b) * lambda;
                for (index, base) in bases.iter().enumerate() {
                    let entry = table.get(variant, index);
                    if !live[index] {
                        assert!(bool::from(entry.y.is_zero()));
                        continue;
                    }
                    let expected = C::from(*base) * mu;
                    let affine = expected.to_affine();
                    let (x, y) = C::affine_xy(&affine);
                    assert_eq!((entry.x, entry.y), (x, y), "variant {variant} ({eta:?})");
                    assert_eq!(entry.zeta_x, x * zeta);
                    for unit in 0..6 {
                        let (ux, uy) = unit_coords(entry, unit);
                        let rotation = [C::ScalarExt::ONE, lambda, lambda * lambda][unit >> 1];
                        let mut unit_scalar = rotation;
                        if unit & 1 == 1 {
                            unit_scalar = -unit_scalar;
                        }
                        let expected_unit = (expected * unit_scalar).to_affine();
                        let (ex, ey) = C::affine_xy(&expected_unit);
                        assert_eq!((ux, uy), (ex, ey), "unit {unit} of variant {variant}");
                    }
                }
            }
        }
    }

    macro_rules! prepared_tests {
        ($mod_name:ident, $curve:ty) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn matches_native() {
                    table_matches_native::<$curve>();
                }
            }
        };
    }

    prepared_tests!(pallas_prepared, pallas::Point);
    prepared_tests!(vesta_prepared, vesta::Point);
}
