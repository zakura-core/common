//! Storage choices shared by compact and expanded multiplication tables.

use core::{fmt, marker::PhantomData};

use super::{AffinePoint, PastaCurve};
use crate::field::{PastaField, Reduced};

/// Exact table length and minimum scratch lengths for curve table preparation.
///
/// All lengths count elements, not bytes. Expanded table preparation can use
/// larger scratch buffers to share inversions across windows; see
/// [`FixedBaseTable::prepare_with`](super::FixedBaseTable::prepare_with).
/// Batch multiplication reports its scratch through
/// [`EisensteinTableBatch::multiplication_scratch`][batch_scratch].
///
/// [batch_scratch]: super::EisensteinTableBatch::multiplication_scratch
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CurveTableRequirements {
    /// Number of entries, in the caller-selected representation.
    pub table_entries: usize,
    /// Minimum number of projective scratch elements.
    pub projective_scratch: usize,
    /// Minimum number of base-field scratch elements.
    pub field_scratch: usize,
}

/// A nonidentity affine point with its endomorphism x-coordinate cached.
///
/// Stores `(x, zeta * x, y)` in [`PastaField`]'s Montgomery representation:
/// 96 bytes with alignment 8, where `zeta` is the coordinate field's
/// [`PastaField::ZETA`] value. All coordinates must be reduced, `(x, y)` must
/// satisfy the curve equation, and the cached coordinate must equal `zeta * x`.
/// Constructors establish these invariants. Trusted [`bento::Pod`] storage
/// preserves the representation for direct runtime use on little-endian targets.
///
/// Use [`AffinePoint`] entries to save storage, or this type to avoid field
/// multiplication when a table lookup applies the endomorphism.
// SAFETY: The derive checks padding and field layouts. Every bit pattern is
// safe to read and share; mathematical invariants do not affect memory safety.
#[derive(Clone, Copy, Eq, PartialEq, bento::Pod)]
#[repr(C)]
pub struct PreparedAffinePoint<C: PastaCurve> {
    x: PastaField<C::Base, Reduced>,
    endomorphism_x: PastaField<C::Base, Reduced>,
    y: PastaField<C::Base, Reduced>,
    marker: PhantomData<C>,
}

impl<C: PastaCurve> fmt::Debug for PreparedAffinePoint<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PreparedAffinePoint")
            .field("affine", &self.to_affine())
            .field("endomorphism_x", &self.endomorphism_x)
            .finish()
    }
}

impl<C: PastaCurve> PreparedAffinePoint<C> {
    /// Caches the endomorphism coordinate of a valid affine point.
    ///
    /// Assumes [`AffinePoint`]'s mathematical invariants, as do point operations.
    pub fn from_affine(point: &AffinePoint<C>) -> Self {
        Self {
            x: point.x,
            endomorphism_x: point.x.mul(&PastaField::<C::Base>::ZETA).reduce(),
            y: point.y,
            marker: PhantomData,
        }
    }

    /// Returns the underlying affine point by copying `x` and `y`.
    pub const fn to_affine(&self) -> AffinePoint<C> {
        AffinePoint {
            x: self.x,
            y: self.y,
            marker: PhantomData,
        }
    }
}

mod sealed {
    pub trait Entry {}
}

/// A nonidentity affine point with all three endomorphism x-coordinates cached.
///
/// Stores `(x, zeta * x, zeta² * x, y)` in [`PastaField`]'s Montgomery
/// representation: 128 bytes with alignment 8. Here `zeta` is the coordinate
/// field's [`PastaField::ZETA`]. All coordinates must be reduced, `(x, y)` must
/// satisfy [`AffinePoint`]'s curve equation, and both cached coordinates must
/// match the indicated products.
///
/// [`Self::from_affine`] computes the cache, assuming a valid input point.
/// Trusted [`bento::Pod`] storage preserves this representation on little-endian
/// targets without checking the curve equation, coordinate ranges, or caches.
/// This is table storage; use [`AffinePoint::to_bytes`] for protocol encoding.
///
/// This representation trades storage for direct selection of every rotation.
/// [`AffinePoint`] and [`PreparedAffinePoint`] store fewer cached coordinates.
// SAFETY: The derive checks padding and field layouts. Every bit pattern is
// safe to read and share; curve and cache invariants affect only arithmetic.
#[derive(Clone, Copy, Eq, PartialEq, bento::Pod)]
#[repr(C)]
pub struct RotatedAffinePoint<C: PastaCurve> {
    x: [PastaField<C::Base, Reduced>; 3],
    y: PastaField<C::Base, Reduced>,
    marker: PhantomData<C>,
}

impl<C: PastaCurve> fmt::Debug for RotatedAffinePoint<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RotatedAffinePoint")
            .field("affine", &self.to_affine())
            .finish()
    }
}

impl<C: PastaCurve> RotatedAffinePoint<C> {
    /// Caches all endomorphism rotations of a valid nonidentity point.
    ///
    /// Assumes [`AffinePoint`]'s mathematical invariants without revalidation.
    pub fn from_affine(point: &AffinePoint<C>) -> Self {
        let rotated = point.x.mul(&PastaField::<C::Base>::ZETA).reduce();
        Self {
            x: [
                point.x,
                rotated,
                point.x.negate_nonzero().sub_reduced(&rotated),
            ],
            y: point.y,
            marker: PhantomData,
        }
    }

    /// Copies the underlying affine point.
    pub const fn to_affine(&self) -> AffinePoint<C> {
        AffinePoint {
            x: self.x[0],
            y: self.y,
            marker: PhantomData,
        }
    }
}

impl<C: PastaCurve> sealed::Entry for RotatedAffinePoint<C> {}
impl<C: PastaCurve> CurveTableEntry<C> for RotatedAffinePoint<C> {
    fn from_affine(point: &AffinePoint<C>) -> Self {
        Self::from_affine(point)
    }
    fn affine(&self) -> AffinePoint<C> {
        self.to_affine()
    }
    fn rotated(&self, rotation: usize) -> AffinePoint<C> {
        AffinePoint {
            x: self.x[rotation],
            y: self.y,
            marker: PhantomData,
        }
    }
}

/// Selects the stored representation of a curve multiplication table entry.
///
/// This trait is sealed to [`AffinePoint`] (64 bytes),
/// [`PreparedAffinePoint`] (96 bytes), and [`RotatedAffinePoint`] (128 bytes).
/// All implement [`bento::Pod`]. Select the entry type through the table's
/// generic parameter; table preparation constructs the same mathematical layout.
/// Generic callers can initialize entry buffers with [`Self::from_affine`].
///
/// ```
/// use zakura_udon::curve::{
///     AffinePoint, CurveTableEntry, Pallas, PastaCurve, RotatedAffinePoint,
/// };
///
/// fn buffer<C: PastaCurve, E: CurveTableEntry<C>>(base: &AffinePoint<C>) -> [E; 8] {
///     [E::from_affine(base); 8]
/// }
/// let base = AffinePoint::<Pallas>::GENERATOR;
/// let entries = buffer::<Pallas, RotatedAffinePoint<Pallas>>(&base);
/// assert_eq!(entries[0].affine(), base);
/// assert_eq!(entries[0].rotated(1), base.endomorphism());
/// assert_eq!(entries[0].rotated(2), base.endomorphism().endomorphism());
/// ```
pub trait CurveTableEntry<C: PastaCurve>: sealed::Entry + Copy + fmt::Debug + Send + Sync {
    /// Constructs an entry from a point satisfying [`AffinePoint`]'s invariants.
    ///
    /// Copies affine coordinates and computes any cached endomorphism coordinate.
    fn from_affine(point: &AffinePoint<C>) -> Self;

    /// Copies the affine coordinates.
    fn affine(&self) -> AffinePoint<C>;

    /// Applies [`AffinePoint::endomorphism`] `rotation` times.
    ///
    /// Assumes the entry satisfies its type's mathematical invariants, including
    /// cache consistency for [`PreparedAffinePoint`] and [`RotatedAffinePoint`].
    ///
    /// # Panics
    ///
    /// Panics unless `rotation` is in `0..3`.
    fn rotated(&self, rotation: usize) -> AffinePoint<C>;
}

impl<C: PastaCurve> sealed::Entry for AffinePoint<C> {}
impl<C: PastaCurve> sealed::Entry for PreparedAffinePoint<C> {}

impl<C: PastaCurve> CurveTableEntry<C> for AffinePoint<C> {
    fn from_affine(point: &AffinePoint<C>) -> Self {
        *point
    }
    fn affine(&self) -> AffinePoint<C> {
        *self
    }
    fn rotated(&self, rotation: usize) -> AffinePoint<C> {
        match rotation {
            0 => *self,
            1 => self.endomorphism(),
            2 => Self {
                x: self.x.mul(&PastaField::<C::Base>::ZETA_INVERSE).reduce(),
                ..*self
            },
            _ => unreachable!("a cube root has three rotations"),
        }
    }
}

impl<C: PastaCurve> CurveTableEntry<C> for PreparedAffinePoint<C> {
    fn from_affine(point: &AffinePoint<C>) -> Self {
        Self::from_affine(point)
    }
    fn affine(&self) -> AffinePoint<C> {
        self.to_affine()
    }
    fn rotated(&self, rotation: usize) -> AffinePoint<C> {
        // zeta² + zeta + 1 = 0 gives the second rotation without a product.
        let x = match rotation {
            0 => self.x,
            1 => self.endomorphism_x,
            2 => self.x.negate_nonzero().sub_reduced(&self.endomorphism_x),
            _ => unreachable!("a cube root has three rotations"),
        };
        AffinePoint {
            x,
            y: self.y,
            marker: PhantomData,
        }
    }
}
