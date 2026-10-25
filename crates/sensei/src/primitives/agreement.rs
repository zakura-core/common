//! Retained key-agreement preparation and shared-inversion batch operations.
//!
//! Tables cache every endomorphism rotation. Large preparation batches use
//! Udon's affine addition chains, and multiplication borrows retained tables
//! with enough scratch for its synchronized affine ladders.
use super::{Fq, NonIdentityPallasPoint, pallas::Point};
use alloc::{boxed::Box, vec, vec::Vec};
use core::fmt;
use udon::{
    curve::{
        EisensteinScalar, EisensteinTable, EisensteinTableBatch, Pallas, PallasAffine,
        PallasProjective, RotatedAffinePoint,
    },
    exec::{SerialExecutor, TaskBudget},
    field::Fp,
};

/// Entries in one Eisenstein digit-orbit table.
const TABLE_ENTRIES: usize = 8;
type Entry = RotatedAffinePoint<Pallas>;
type Batch<'a> = EisensteinTableBatch<'a, Pallas, Entry>;

/// A scalar with its reusable Eisenstein digit schedule.
///
/// Clones contain the scalar and its derived schedule and are not zeroized on
/// drop; [`core::fmt::Debug`] redacts both.
#[derive(Clone)]
pub struct PreparedScalar {
    scalar: Fq,
    schedule: EisensteinScalar<Pallas>,
}
impl fmt::Debug for PreparedScalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PreparedScalar")
            .field("scalar", &"<redacted>")
            .field("schedule", &"<redacted>")
            .finish()
    }
}
impl PreparedScalar {
    /// Recodes this scalar once for use across agreement calls.
    pub fn new(scalar: Fq) -> Self {
        Self {
            scalar,
            schedule: EisensteinScalar::new(&scalar.native()),
        }
    }
    /// Returns the original scalar without recoding or serializing it.
    pub fn scalar(&self) -> Fq {
        self.scalar
    }
    /// Multiplies unprepared projective bases using the effective-affine path.
    ///
    /// Returns one point per base in slice order, or an empty vector for no bases.
    pub fn multiply_unprepared(&self, bases: &[Point]) -> Vec<Point> {
        let mut output: Vec<_> = bases.iter().map(|p| p.native()).collect();
        let size =
            udon::curve::same_scalar_scratch::<Pallas>(bases.len()).expect("allocated bases");
        udon::curve::batch_mul_same_scalar_prepared(
            &mut output,
            &self.schedule,
            &mut vec![Fp::ZERO; size],
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        output.into_iter().map(Point::from_native).collect()
    }
}

/// An owned table retaining all three endomorphism rotations of every entry.
///
/// Each instance owns its heap allocation until dropped. Cloning allocates and
/// copies the full table into an independent owner. Multiplication borrows the
/// retained entries without copying or rebuilding them.
#[derive(Clone, Debug)]
pub struct PreparedBase {
    entries: Box<[Entry; TABLE_ENTRIES]>,
}
impl PreparedBase {
    /// Heap storage retained by one table, excluding its owner.
    pub const TABLE_BYTES: usize = core::mem::size_of::<[Entry; TABLE_ENTRIES]>();

    /// Prepares one nonidentity base.
    pub fn new(base: NonIdentityPallasPoint) -> Self {
        let base = *base.native().as_affine().expect("nonidentity type");
        let mut entries = Box::new([Entry::from_affine(&base); TABLE_ENTRIES]);
        EisensteinTable::prepare(
            &base,
            &mut entries,
            &mut [PallasProjective::IDENTITY; TABLE_ENTRIES],
            &mut [Fp::ZERO; TABLE_ENTRIES],
        );
        Self { entries }
    }
    /// Prepares a batch using affine addition chains for large batches.
    ///
    /// Returns one independently owned table per base, in slice order. An empty
    /// input returns an empty vector; the tables retain no borrow of `bases`.
    ///
    /// The caller filters invalid encodings before calling this function; the
    /// number of live bases determines the preparation path, not container size.
    pub fn batch(bases: &[NonIdentityPallasPoint]) -> Vec<Self> {
        if bases.is_empty() {
            return Vec::new();
        }
        let bases: Vec<_> = bases
            .iter()
            .map(|base| *base.native().as_affine().expect("nonidentity type"))
            .collect();
        let requirements = Batch::requirements(bases.len()).expect("representable tables");
        let mut entries =
            vec![Entry::from_affine(&PallasAffine::GENERATOR); requirements.table_entries];
        Batch::prepare(
            &bases,
            &mut entries,
            &mut vec![PallasProjective::IDENTITY; requirements.projective_scratch],
            &mut vec![Fp::ZERO; requirements.field_scratch],
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        // Move the newly constructed entries into independently retained owners.
        // Subsequent multiplication borrows those owners without table copies.
        let mut entries = entries.into_iter();
        bases
            .iter()
            .map(|_| Self {
                entries: Box::new(core::array::from_fn(|_| entries.next().unwrap())),
            })
            .collect()
    }
    fn table(&self) -> EisensteinTable<'_, Pallas, Entry> {
        use udon::curve::CurveTableEntry;
        EisensteinTable::bind(&self.entries[0].affine(), &self.entries)
    }
    /// Multiplies this retained table with the retained scalar schedule.
    pub fn multiply(&self, scalar: &PreparedScalar) -> Point {
        Point::from_native(self.table().mul_prepared(&scalar.schedule))
    }
    /// Multiplies borrowed tables with synchronized ladders and shared inversions.
    ///
    /// Repeated references, independently allocated tables, and empty batches
    /// are supported. Table entries and scalar schedules are never rebuilt.
    /// Returns one point per table reference in slice order, including repeated
    /// references, or an empty vector for no tables.
    pub fn multiply_batch(tables: &[&Self], scalar: &PreparedScalar) -> Vec<Point> {
        let views: Vec<_> = tables.iter().map(|table| table.table()).collect();
        let refs: Vec<_> = views.iter().collect();
        let mut output = vec![PallasProjective::IDENTITY; tables.len()];
        let size = Batch::multiplication_scratch(tables.len()).expect("representable output");
        Batch::mul_borrowed_prepared(
            &refs,
            &scalar.schedule,
            &mut output,
            &mut vec![Fp::ZERO; size],
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        output.into_iter().map(Point::from_native).collect()
    }
}
