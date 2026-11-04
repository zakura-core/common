//! Canonical affine points for the SRS, Sinsemilla table, and historical keys.
//!
//! Each record is exactly 64 bytes: canonical little-endian `x`, then `y`.
//! Decoding checks the record count, field residues, and curve membership;
//! affine records cannot represent the identity. The caller's expected curve
//! type determines which Pasta base field is decoded.

use udon::{
    curve::{AffinePoint, PastaCurve},
    field::{PastaField, Reduced},
};

use crate::{Error, RawStore};

/// Vesta SRS points in ascending coefficient-degree order.
pub(crate) const COEFFICIENT_BASES: &str = "srs-coefficient-bases.points";
/// Pallas lookup generators in Sinsemilla table-row order.
pub(crate) const SINSEMILLA_GENERATORS: &str = "sinsemilla-generators.points";
/// Historical NU6.2 fixed and permutation commitments, in key order.
pub(crate) const VERIFIER_FIXED: &str = "verifier-fixed.points";
/// Historical pre-NU6.2 fixed and permutation commitments, in key order.
pub(crate) const VERIFIER_INSECURE: &str = "verifier-insecure.points";

/// Canonical little-endian base-field coordinate width.
const COORDINATE_BYTES: usize = 32;
/// Two canonical 32-byte coordinates per affine point.
const POINT_BYTES: usize = 64;

/// Decodes one raw file of canonical affine records into validated points.
pub(crate) fn decode_points<C: PastaCurve>(
    raw: &RawStore,
    name: &str,
    expected: usize,
) -> Result<Vec<AffinePoint<C>>, Error> {
    let bytes = raw.bytes(name)?;
    if bytes.len() != expected * POINT_BYTES {
        return Err(Error::new(format!(
            "raw input {name}: expected {expected} 64-byte records, found {} bytes",
            bytes.len()
        )));
    }
    bytes
        .chunks_exact(POINT_BYTES)
        .enumerate()
        .map(|(index, record)| {
            let decode = |half: &[u8]| {
                PastaField::<C::Base, Reduced>::from_bytes(half.try_into().expect("32-byte half"))
            };
            let (x, y) = (
                decode(&record[..COORDINATE_BYTES]),
                decode(&record[COORDINATE_BYTES..]),
            );
            x.zip(y)
                .and_then(|(x, y)| AffinePoint::from_xy(x, y))
                .ok_or_else(|| {
                    Error::new(format!(
                        "raw input {name}, record {index}: not a canonical nonidentity curve point"
                    ))
                })
        })
        .collect()
}
