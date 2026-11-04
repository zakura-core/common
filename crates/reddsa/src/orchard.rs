//! Signature types for the Orchard protocol.
//!
//! With `pallas-sensei`, Pallas operations use Sensei/Udon variable-time
//! arithmetic. Secret-key operations have the timing assumptions documented
//! by that implementation’s RedPallas module.

#[cfg(feature = "alloc")]
use alloc::vec::Vec;
#[cfg(feature = "alloc")]
use core::borrow::Borrow;

#[cfg(feature = "pallas-pasta")]
use group::GroupEncoding as _;
#[cfg(all(feature = "pallas-pasta", feature = "alloc"))]
use group::{Group as _, ff::PrimeField as _};
#[cfg(feature = "pallas-pasta")]
use pasta_curves::{glv::Table, pallas};
#[cfg(feature = "pallas-sensei")]
use sensei::primitives::pallas;

use crate::{SigType, private};

#[cfg(feature = "alloc")]
use crate::scalar_mul::{LookupTable5, NonAdjacentForm, VartimeMultiscalarMul};

#[cfg(test)]
mod tests;

/// The byte-encoding of the basepoint for the Orchard `SpendAuthSig` on the [Pallas curve][pallasandvesta].
///
/// [pallasandvesta]: https://zips.z.cash/protocol/nu5.pdf#pallasandvesta
// Reproducible by pallas::Point::hash_to_curve("z.cash:Orchard")(b"G").to_bytes()
const ORCHARD_SPENDAUTHSIG_BASEPOINT_BYTES: [u8; 32] = [
    99, 201, 117, 184, 132, 114, 26, 141, 12, 161, 112, 123, 227, 12, 127, 12, 95, 68, 95, 62, 124,
    24, 141, 59, 6, 214, 241, 40, 179, 35, 85, 183,
];

/// The byte-encoding of the basepoint for the Orchard `BindingSig` on the Pallas curve.
// Reproducible by pallas::Point::hash_to_curve("z.cash:Orchard-cv")(b"r").to_bytes()
const ORCHARD_BINDINGSIG_BASEPOINT_BYTES: [u8; 32] = [
    145, 90, 60, 136, 104, 198, 195, 14, 47, 128, 144, 238, 69, 215, 110, 64, 72, 32, 141, 234, 91,
    35, 102, 79, 187, 9, 164, 15, 85, 68, 244, 7,
];

/// A type variable corresponding to Zcash's `OrchardSpendAuthSig`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SpendAuth {}
// This should not exist, but is necessary to use zeroize::DefaultIsZeroes.
impl Default for SpendAuth {
    fn default() -> Self {
        unimplemented!()
    }
}
impl SigType for SpendAuth {}
impl super::SpendAuth for SpendAuth {}

/// A type variable corresponding to Zcash's `OrchardBindingSig`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Binding {}
// This should not exist, but is necessary to use zeroize::DefaultIsZeroes.
impl Default for Binding {
    fn default() -> Self {
        unimplemented!()
    }
}
impl SigType for Binding {}
impl super::Binding for Binding {}

impl private::Sealed<SpendAuth> for SpendAuth {
    const H_STAR_PERSONALIZATION: &'static [u8; 16] = b"Zcash_RedPallasH";
    type Point = pallas::Point;
    type Scalar = pallas::Scalar;

    fn basepoint() -> pallas::Point {
        pallas::Point::from_bytes(&ORCHARD_SPENDAUTHSIG_BASEPOINT_BYTES).unwrap()
    }

    #[cfg(feature = "pallas-pasta")]
    fn basepoint_mul_vartime(scalar: pallas::Scalar) -> pallas::Point {
        #[cfg(target_has_atomic = "ptr")]
        static TABLE: once_cell::race::OnceBox<Table<pallas::Point>> =
            once_cell::race::OnceBox::new();
        basepoint_mul_vartime::<SpendAuth>(
            #[cfg(target_has_atomic = "ptr")]
            &TABLE,
            &scalar,
        )
    }
    #[cfg(all(feature = "alloc", feature = "pallas-pasta"))]
    fn batch_decode_points(
        items: impl Iterator<Item = [u8; 32]>,
    ) -> Option<Vec<Option<pallas::Point>>> {
        batch_decode_pallas_points(items)
    }
}
impl private::Sealed<Binding> for Binding {
    const H_STAR_PERSONALIZATION: &'static [u8; 16] = b"Zcash_RedPallasH";
    type Point = pallas::Point;
    type Scalar = pallas::Scalar;

    fn basepoint() -> pallas::Point {
        pallas::Point::from_bytes(&ORCHARD_BINDINGSIG_BASEPOINT_BYTES).unwrap()
    }

    #[cfg(feature = "pallas-pasta")]
    fn basepoint_mul_vartime(scalar: pallas::Scalar) -> pallas::Point {
        #[cfg(target_has_atomic = "ptr")]
        static TABLE: once_cell::race::OnceBox<Table<pallas::Point>> =
            once_cell::race::OnceBox::new();
        basepoint_mul_vartime::<Binding>(
            #[cfg(target_has_atomic = "ptr")]
            &TABLE,
            &scalar,
        )
    }
    #[cfg(all(feature = "alloc", feature = "pallas-pasta"))]
    fn batch_decode_points(
        items: impl Iterator<Item = [u8; 32]>,
    ) -> Option<Vec<Option<pallas::Point>>> {
        batch_decode_pallas_points(items)
    }
}

/// Batches with fewer point encodings than this decode on the calling
/// thread. Each decode is a square root, a few microseconds, so smaller
/// batches would spend more waking pool workers than they save.
#[cfg(all(feature = "alloc", feature = "pallas-pasta", feature = "multicore"))]
const MIN_PARALLEL_DECODE_POINTS: usize = 16;

/// Encodings per parallel task: one full batch of the decoder's lanes.
#[cfg(all(feature = "alloc", feature = "pallas-pasta", feature = "multicore"))]
const DECODE_LANES: usize = 8;

/// Decodes a batch's point encodings (each signature's `R`, plus any keys
/// still held as bytes) together.
///
/// Points decode through [`pasta_curves::arithmetic::CurveAffine::batch_decode`],
/// which computes several square roots at once. With the `multicore` feature,
/// a pool of two or more threads, and at least
/// [`MIN_PARALLEL_DECODE_POINTS`] encodings, the batch is also split across
/// the pool, one task per [`DECODE_LANES`] encodings.
/// Results are returned in input order, each equal to `from_bytes` of its
/// encoding, and consumed in the verifier's order, so a batch with a
/// malformed encoding reports the same error as decoding one at a time.
#[cfg(all(feature = "alloc", feature = "pallas-pasta"))]
fn batch_decode_pallas_points(
    items: impl Iterator<Item = [u8; 32]>,
) -> Option<Vec<Option<pallas::Point>>> {
    use pasta_curves::arithmetic::CurveAffine as _;

    fn decode(encodings: &[[u8; 32]]) -> Vec<Option<pallas::Point>> {
        pallas::Affine::batch_decode(encodings)
            .into_iter()
            .map(|point| Option::<pallas::Affine>::from(point).map(pallas::Point::from))
            .collect()
    }

    let encodings = items.collect::<Vec<_>>();
    #[cfg(feature = "multicore")]
    {
        use maybe_rayon::prelude::*;

        if maybe_rayon::current_num_threads() >= 2 && encodings.len() >= MIN_PARALLEL_DECODE_POINTS
        {
            // One decoder batch per task keeps every worker busy; each task is
            // tens of microseconds, far above the pool's scheduling cost.
            return Some(
                encodings
                    .par_chunks(DECODE_LANES)
                    .map(decode)
                    .collect::<Vec<_>>()
                    .concat(),
            );
        }
    }
    Some(decode(&encodings))
}

/// Variable-time `[scalar]B` through a GLV table for `T`'s basepoint.
///
/// With pointer atomics the table is built once and cached in `table`;
/// racing first uses may each build one, and all but one are discarded.
/// Without them it is rebuilt on each call.
#[cfg(feature = "pallas-pasta")]
fn basepoint_mul_vartime<T: SigType + private::Sealed<T, Point = pallas::Point>>(
    #[cfg(target_has_atomic = "ptr")] table: &once_cell::race::OnceBox<Table<pallas::Point>>,
    scalar: &pallas::Scalar,
) -> pallas::Point {
    #[cfg(target_has_atomic = "ptr")]
    let table = table.get_or_init(|| alloc::boxed::Box::new(Table::new(&T::basepoint())));
    #[cfg(not(target_has_atomic = "ptr"))]
    let table = &Table::new(&T::basepoint());
    table.mul(scalar)
}

#[cfg(feature = "alloc")]
impl NonAdjacentForm for pallas::Scalar {
    fn inner_to_bytes(&self) -> [u8; 32] {
        self.to_repr()
    }

    /// The NAF length for Pallas is 255 since Pallas' order is about 2<sup>254</sup> +
    /// 2<sup>125.1</sup>.
    fn naf_length() -> usize {
        255
    }
}

#[cfg(feature = "alloc")]
impl<'a> From<&'a pallas::Point> for LookupTable5<pallas::Point> {
    #[allow(non_snake_case)]
    fn from(A: &'a pallas::Point) -> Self {
        let mut Ai = [*A; 8];
        let A2 = A.double();
        for i in 0..7 {
            Ai[i + 1] = A2 + Ai[i];
        }
        // Now Ai = [A, 3A, 5A, 7A, 9A, 11A, 13A, 15A]
        LookupTable5(Ai)
    }
}

#[cfg(feature = "alloc")]
impl VartimeMultiscalarMul for pallas::Point {
    type Scalar = pallas::Scalar;
    type Point = pallas::Point;

    #[allow(non_snake_case)]
    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<pallas::Point>
    where
        I: IntoIterator,
        I::Item: Borrow<Self::Scalar>,
        J: IntoIterator<Item = Option<pallas::Point>>,
    {
        #[cfg(feature = "pallas-pasta")]
        {
            pasta_multiscalar_mul(scalars, points)
        }
        #[cfg(not(feature = "pallas-pasta"))]
        {
            wnaf_multiscalar_mul(scalars, points)
        }
    }
}

/// Batches below this many terms evaluate on the calling thread: waking pool
/// workers costs more than splitting such a small multiplication saves.
#[cfg(all(feature = "alloc", feature = "pallas-pasta"))]
const MIN_PARALLEL_MSM_TERMS: usize = 16;

/// Evaluates the MSM with pasta's shared `best_multiexp_vartime`, the one
/// halo2 uses: GLV backends where its planner selects them, the Signed-Booth
/// bucket method otherwise, on the Rayon pool under the `multicore` feature.
#[cfg(all(feature = "alloc", feature = "pallas-pasta"))]
fn pasta_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<pallas::Point>
where
    I: IntoIterator,
    I::Item: Borrow<pallas::Scalar>,
    J: IntoIterator<Item = Option<pallas::Point>>,
{
    use group::{Curve as _, CurveAffine as _};
    use pasta_curves::arithmetic::best_multiexp_vartime_with_parallelism;

    let points = points.into_iter().collect::<Option<Vec<_>>>()?;
    let scalars = scalars.into_iter().map(|c| *c.borrow()).collect::<Vec<_>>();
    assert_eq!(scalars.len(), points.len());

    let mut affine = vec![pallas::Affine::identity(); points.len()];
    pallas::Point::batch_normalize(&points, &mut affine);
    Some(best_multiexp_vartime_with_parallelism(
        &scalars,
        &affine,
        scalars.len() >= MIN_PARALLEL_MSM_TERMS,
    ))
}

/// Interleaved width-5 wNAF over projective lookup tables (the Sensei
/// backend's MSM, and the reference for the pasta path's tests).
#[cfg(all(feature = "alloc", any(test, not(feature = "pallas-pasta"))))]
#[allow(non_snake_case)]
fn wnaf_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<pallas::Point>
where
    I: IntoIterator,
    I::Item: Borrow<pallas::Scalar>,
    J: IntoIterator<Item = Option<pallas::Point>>,
{
    {
        let nafs: Vec<_> = scalars
            .into_iter()
            .map(|c| c.borrow().non_adjacent_form(5))
            .collect();

        let lookup_tables = points
            .into_iter()
            .map(|P_opt| P_opt.map(|P| LookupTable5::<pallas::Point>::from(&P)))
            .collect::<Option<Vec<_>>>()?;

        let mut r = pallas::Point::identity();
        let naf_size = pallas::Scalar::naf_length();

        for i in (0..naf_size).rev() {
            let mut t = r.double();

            for (naf, lookup_table) in nafs.iter().zip(lookup_tables.iter()) {
                #[allow(clippy::comparison_chain)]
                if naf[i] > 0 {
                    t += lookup_table.select(naf[i] as usize);
                } else if naf[i] < 0 {
                    t -= lookup_table.select(-naf[i] as usize);
                }
            }

            r = t;
        }

        Some(r)
    }
}
