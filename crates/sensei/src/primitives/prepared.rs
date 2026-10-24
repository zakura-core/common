//! Owned multiplication preparation, with no circuit, SRS, or worker dependency.
use alloc::vec;
use alloc::vec::Vec;
use udon::{
    curve::{
        AffinePoint, FixedBaseDescription, FixedBaseTable, PastaCurve, PreparedAffinePoint,
        ProjectivePoint,
    },
    field::PastaField,
};

/// Owns a fixed-base table and the descriptor needed to borrow it for use.
///
/// Entries must encode this base in the descriptor's order. Construction from
/// entries trusts the caller; Udon's binding checks lengths, not curve points or
/// table multiples. Multiplication inherits Udon's variable-time behavior.
pub(crate) struct Generator<C: PastaCurve> {
    base: AffinePoint<C>,
    description: FixedBaseDescription,
    entries: Vec<PreparedAffinePoint<C>>,
}

impl<C: PastaCurve> Generator<C> {
    pub(crate) fn new(base: AffinePoint<C>) -> Self {
        let description = FixedBaseDescription::default();
        let sizes = description.requirements().expect("fixed width");
        let mut entries = vec![PreparedAffinePoint::from_affine(&base); sizes.table_entries];
        FixedBaseTable::prepare_with(
            description,
            &base,
            &mut entries,
            &mut vec![ProjectivePoint::IDENTITY; sizes.projective_scratch],
            &mut vec![PastaField::ZERO; sizes.field_scratch],
        )
        .expect("fixed sizes");
        Self::from_entries(base, description, entries)
    }

    /// Takes ownership of trusted entries prepared for `base` and `description`.
    ///
    /// No validation runs here. A wrong length panics when [`Self::table`] is
    /// used; wrong entry values can silently produce incorrect products.
    pub(crate) fn from_entries(
        base: AffinePoint<C>,
        description: FixedBaseDescription,
        entries: Vec<PreparedAffinePoint<C>>,
    ) -> Self {
        Self {
            base,
            description,
            entries,
        }
    }

    pub(crate) fn table(&self) -> FixedBaseTable<'_, C, PreparedAffinePoint<C>> {
        FixedBaseTable::bind(self.description, &self.base, &self.entries)
            .expect("prepared generator")
    }

    pub(crate) fn mul(&self, scalar: &PastaField<C::Scalar>) -> ProjectivePoint<C> {
        self.table().mul(scalar)
    }
}
