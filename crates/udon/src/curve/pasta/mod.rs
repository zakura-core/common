//! Pasta point representations, parameters, and optimized curve arithmetic.

#![forbid(unsafe_code)]

use core::{fmt, marker::PhantomData};

use crate::checks::{assert_length, assert_scratch};
use crate::field::{PastaField, Reduced, ReductionState};

mod affine;
pub(crate) mod batch;
pub(crate) mod digits;
mod effective;
pub(crate) mod eisenstein;
pub(crate) mod eisenstein_batch;
mod encoding;
mod fixed_base;
pub(crate) mod glv;
pub(crate) mod parameters;
mod point;
mod projective;
pub(crate) mod reduce;
mod table_entry;

pub use batch::batch_normalize;
pub use effective::{batch_mul_same_scalar, batch_mul_same_scalar_prepared, same_scalar_scratch};
pub use eisenstein::{EisensteinScalar, EisensteinTable};
pub use eisenstein_batch::EisensteinTableBatch;
pub use fixed_base::{FixedBaseDescription, FixedBaseTable};
pub use glv::glv_decompose;
pub use parameters::{Pallas, PastaCurve, Vesta};
pub use table_entry::{
    CurveTableEntry, CurveTableRequirements, PreparedAffinePoint, RotatedAffinePoint,
};

#[cfg(test)]
pub(crate) mod test_reference;
#[cfg(test)]
mod tests;

/// A nonidentity Pasta point in affine coordinates.
///
/// The stored layout is `x` followed by `y`, each in [`PastaField`]'s four-limb
/// Montgomery representation: 64 bytes with alignment 8. Bento storage requires
/// a little-endian target. Coordinates use [`Reduced`] residues satisfying
/// `y² = x³ + 5`. Constructors establish these invariants; trusted [`bento::Pod`]
/// storage preserves them without runtime validation.
///
/// Use [`Self::from_bytes`] to decode untrusted protocol inputs. POD byte
/// views do not validate coordinate ranges or curve membership.
///
/// Use [`Self::to_bytes`] for protocol encoding. [`crate::STORED_FORM`]
/// identifies the field representation only; artifact owners must separately
/// identify the curve and their record schema.
// SAFETY: The derive checks the coordinate fields and zero-sized marker for
// POD layout, including the absence of padding. Every coordinate bit pattern
// is valid to read and share. Curve operations use safe Rust; curve membership
// and reduced residues are mathematical requirements, not memory-safety ones.
// Future unsafe kernels must remain memory-safe for arbitrary coordinates.
#[derive(Clone, Copy, Eq, PartialEq, bento::Pod)]
#[repr(C)]
pub struct AffinePoint<C: PastaCurve> {
    x: PastaField<C::Base, Reduced>,
    y: PastaField<C::Base, Reduced>,
    marker: PhantomData<C>,
}

/// An affine Pasta point, including identity.
///
/// [`Default`] returns identity. Coordinates of a nonidentity point obey
/// [`AffinePoint`]'s invariants. This type does not implement [`bento::Pod`];
/// store nonidentity [`AffinePoint`] values or use [`Self::to_bytes`].
///
/// Addition, subtraction, and doubling return [`ProjectivePoint`] without
/// inversion. Keep intermediate results projective, then use [`batch_normalize`]
/// for several affine outputs or [`ProjectivePoint::to_point`] for one.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Point<C: PastaCurve>(Option<AffinePoint<C>>);

/// A Pasta point represented by Jacobian coordinates `(x, y, z)`.
///
/// For nonzero `z`, the affine coordinates are `(x / z², y / z³)` and satisfy
/// the curve equation. Every `z = 0` representation denotes identity, which is
/// also the [`Default`]. Equality compares group elements without inversion,
/// including differently scaled representations. Group operations do not
/// promise a particular scaling of their result.
///
/// This type does not implement [`bento::Pod`]; store [`AffinePoint`] values
/// instead.
#[derive(Clone, Copy)]
pub struct ProjectivePoint<C: PastaCurve> {
    x: PastaField<C::Base>,
    y: PastaField<C::Base>,
    z: PastaField<C::Base>,
    marker: PhantomData<C>,
}

/// The point and slopes returned by [`ProjectivePoint::incomplete_double_and_add`].
///
/// `A` is the projective input and `B` is the nonidentity affine input.
#[derive(Clone, Copy, Debug)]
pub struct IncompleteDoubleAndAdd<C: PastaCurve> {
    /// The nonidentity result `A + (A + B)`.
    pub point: ProjectivePoint<C>,
    /// Numerators of the slopes for `A + B`, then `A + (A + B)`, in that order.
    ///
    /// With `R = A + B`, the slopes are `(B.y - A.y) / (B.x - A.x)` and
    /// `(R.y - A.y) / (R.x - A.x)`, using affine coordinates.
    /// Both use the returned point's nonzero Jacobian `z` coordinate as their
    /// denominator, available through [`ProjectivePoint::coordinates`]. Retain
    /// that denominator if replacing `point` before recovering the slopes.
    pub slope_numerators: [PastaField<C::Base>; 2],
}

/// A nonidentity affine Pallas point over [`crate::field::Fp`].
pub type PallasAffine = AffinePoint<Pallas>;
/// An affine Pallas point, including identity.
pub type PallasPoint = Point<Pallas>;
/// A Jacobian Pallas point.
pub type PallasProjective = ProjectivePoint<Pallas>;
/// A nonidentity affine Vesta point over [`crate::field::Fq`].
pub type VestaAffine = AffinePoint<Vesta>;
/// An affine Vesta point, including identity.
pub type VestaPoint = Point<Vesta>;
/// A Jacobian Vesta point.
pub type VestaProjective = ProjectivePoint<Vesta>;

/// Returns `x³ + 5`, the right-hand side of both Pasta curve equations.
fn curve_rhs<C: PastaCurve>(x: &PastaField<C::Base, impl ReductionState>) -> PastaField<C::Base> {
    x.square().mul(x).add(&AffinePoint::<C>::B)
}

/// A rejected curve operation or multiplication table description.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CurveError {
    /// The window width is unsupported by the requested operation.
    InvalidWindowBits {
        /// The supplied width.
        bits: u32,
    },
    /// A scalar is not below its modulus, exceeds its bit bound, or has an
    /// invalid bound.
    InvalidScalar {
        /// Position of the invalid scalar (zero for an invalid bound).
        position: usize,
    },
    /// The planner found no layout within the caller's temporary byte ceiling.
    ///
    /// The search follows [`crate::exec::ExecutionOptions`] and is not
    /// exhaustive; this does not establish a global minimum storage requirement.
    MemoryLimit {
        /// Supplied byte ceiling.
        limit: usize,
        /// Arithmetic workspace bytes required at the planner's stopping point.
        /// An unrepresentable total is reported as `usize::MAX`.
        required: usize,
    },
    /// A requested buffer length cannot be represented by a Rust slice.
    SizeOverflow,
    /// A strided MSM matrix addresses beyond its borrowed base storage.
    MatrixTooSmall {
        /// Number of bases needed to include the last addressed entry.
        required: usize,
        /// Number of available bases.
        provided: usize,
    },
    /// An indexed MSM refers past the end of its base slice.
    BaseIndexOutOfBounds {
        /// Position in the index slice.
        position: usize,
        /// Supplied base index.
        index: u32,
        /// Number of available bases.
        bases: usize,
    },
    /// No MSM implementation fits the supplied scratch capacities.
    ScratchTooSmall {
        /// The buffer's role.
        buffer: &'static str,
        /// Minimum length in elements.
        required: usize,
        /// Supplied length in elements.
        provided: usize,
    },
}

impl fmt::Display for CurveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidWindowBits { bits } => write!(f, "unsupported window width {bits}"),
            Self::InvalidScalar { position } => {
                write!(f, "invalid MSM scalar at position {position}")
            }
            Self::MemoryLimit { limit, required } => {
                write!(f, "MSM needs {required} temporary bytes, limit is {limit}")
            }
            Self::SizeOverflow => f.write_str("curve buffer size overflows a slice length"),
            Self::MatrixTooSmall { required, provided } => {
                write!(f, "MSM matrix needs {required} bases, got {provided}")
            }
            Self::BaseIndexOutOfBounds {
                position,
                index,
                bases,
            } => {
                write!(
                    f,
                    "base index {index} at position {position} exceeds {bases} bases"
                )
            }
            Self::ScratchTooSmall {
                buffer,
                required,
                provided,
            } => {
                write!(
                    f,
                    "{buffer} scratch length is {provided}, requires at least {required}"
                )
            }
        }
    }
}

impl core::error::Error for CurveError {}

pub(crate) const fn checked_count<T>(count: usize, per_item: usize) -> Result<usize, CurveError> {
    match count.checked_mul(per_item) {
        Some(length) if length <= isize::MAX as usize / core::mem::size_of::<T>() => Ok(length),
        _ => Err(CurveError::SizeOverflow),
    }
}
