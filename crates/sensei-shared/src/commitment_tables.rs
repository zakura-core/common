//! Shared layout and preparation of optional commitment acceleration tables.
//!
//! Embedded entries are always affine `(x, y)`. Runtime owners can add cached
//! endomorphism coordinates without changing the deterministic point layout.

use crate::N;
use alloc::{vec, vec::Vec};
use udon::{
    curve::{
        CurveTableEntry, CurveTableRequirements, EisensteinTableBatch, FixedBaseDescription,
        FixedBaseTable, PreparedAffinePoint, Vesta, VestaAffine, VestaProjective,
    },
    exec::{SerialExecutor, TaskBudget},
    field::Fq,
    msm::{AlphaCodebook, AlphaCoefficient, AlphaDescription, AlphaTable, OddTable},
};

/// When to generate an expanded point bank.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Preparation {
    /// Store affine entries in the executable; cache rotations during warmup.
    Embed,
    /// Compute and retain entries during warmup.
    WarmUp,
}
/// Independent preparation choice for each SRS bank.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SrsTable {
    /// Original points only.
    None,
    /// Eight Eisenstein representatives per base.
    Compact,
    /// Sixteen α representatives per base.
    Alpha5,
    /// Thirty-two α representatives per base.
    Alpha6,
    /// Sixty-four α representatives per base.
    Alpha7,
}
impl SrsTable {
    /// α window width, or zero for the other representations.
    pub const fn alpha_width(self) -> u8 {
        match self {
            Self::Alpha5 => 5,
            Self::Alpha6 => 6,
            Self::Alpha7 => 7,
            _ => 0,
        }
    }
    /// Retained expanded entries; original points are accounted separately.
    pub const fn entries(self) -> usize {
        self.requirements::<PreparedAffinePoint<Vesta>>()
            .table_entries
    }
    const fn requirements<E: CurveTableEntry<Vesta>>(self) -> CurveTableRequirements {
        let required = match self {
            Self::None => {
                return CurveTableRequirements {
                    table_entries: 0,
                    projective_scratch: 0,
                    field_scratch: 0,
                };
            }
            Self::Compact => EisensteinTableBatch::<Vesta, E>::requirements(N),
            _ => {
                let description = match AlphaDescription::new(self.alpha_width()) {
                    Ok(description) => description,
                    Err(_) => panic!("invalid SRS table width"),
                };
                description.requirements::<Vesta, E>(N)
            }
        };
        match required {
            Ok(required) => required,
            Err(_) => panic!("SRS table size overflow"),
        }
    }
}
/// Preparation and memory allowance for one SRS expansion.
#[derive(Clone, Copy, Debug)]
pub struct BankPolicy {
    /// Point representation.
    pub table: SrsTable,
    /// Point generation location.
    pub preparation: Preparation,
    /// Ceiling on cached point bytes, excluding shared codebooks.
    pub max_bytes: usize,
}
/// Expanded signed-window preparation of a single generator.
#[derive(Clone, Copy, Debug)]
pub struct FixedPolicy {
    /// Signed window width in `2..=8`.
    pub width: u32,
    /// Point generation location.
    pub preparation: Preparation,
}
impl FixedPolicy {
    /// Exact number of entries.
    ///
    /// # Panics
    ///
    /// Panics if `width` is outside `2..=8`.
    pub const fn entries(self) -> usize {
        match (FixedBaseDescription {
            window_bits: self.width,
        })
        .requirements()
        {
            Ok(requirements) => requirements.table_entries,
            Err(_) => panic!("invalid fixed generator width"),
        }
    }
}
/// Optional shared wNAF folding table.
#[derive(Clone, Copy, Debug)]
pub struct FoldingPolicy {
    /// wNAF width in `2..=8`.
    pub width: u8,
    /// Borrow α odd layers when the coefficient width is sufficient.
    pub reuse_alpha: bool,
    /// Generation location when a separate bank is needed.
    pub preparation: Preparation,
}
/// Order of the optional affine sections: coefficient, Lagrange, W, U, G₀,
/// H, the eleven mask generators G₁, G₂, G₄, …, G₁₀₂₄, and a separate
/// folding odd-multiple bank when requested.
#[derive(Clone, Copy, Debug)]
pub struct Config {
    /// Independent coefficient and Lagrange policies, in that order.
    pub srs: [BankPolicy; 2],
    /// Independent W, U, G₀ and H policies, in that order.
    pub fixed: [FixedPolicy; 4],
    /// Optional eleven-generator mask bank.
    pub sparse: Option<FixedPolicy>,
    /// Shared-scalar folding acceleration; absent selects the general MSM path.
    pub folding: Option<FoldingPolicy>,
    /// Aggregate ceiling on retained expansion and shared codebook payloads.
    pub max_bytes: usize,
}
/// Number of independently addressable sections.
pub const SECTIONS: usize = 18;

// Inclusive section boundaries in the concatenated affine artifact.
const SRS_START: usize = 0;
const SRS_END: usize = 1;
const FIXED_START: usize = 2;
const FIXED_END: usize = 5;
const SPARSE_START: usize = 6;
const SPARSE_END: usize = 16;
const FOLDING_SECTION: usize = 17;

// Retained payload sizes for prepared points and shared alpha codebooks.
const PREPARED_AFFINE_ENTRY_BYTES: usize = 96;
const ALPHA_CODE_BYTES: usize = 4;
const ALPHA_COEFFICIENT_BYTES: usize = 12;

impl Config {
    /// Entries in one section, whether embedded or prepared during warmup.
    /// `section` is in `0..SECTIONS`, in the order described by [`Config`].
    ///
    /// # Panics
    ///
    /// Panics if `section >= SECTIONS` or the selected section's fixed, sparse,
    /// or folding width is outside `2..=8`, even when folding reuses α layers.
    pub const fn entries(self, section: usize) -> usize {
        match section {
            SRS_START..=SRS_END => self.srs[section].table.entries(),
            FIXED_START..=FIXED_END => self.fixed[section - FIXED_START].entries(),
            SPARSE_START..=SPARSE_END => match self.sparse {
                Some(p) => p.entries(),
                None => 0,
            },
            FOLDING_SECTION => match self.folding {
                Some(p) => {
                    let required = match OddTable::<Vesta, PreparedAffinePoint<Vesta>>::requirements(
                        p.width, N,
                    ) {
                        Ok(required) => required,
                        Err(_) => panic!("invalid folding table dimensions"),
                    };
                    if p.reuse_alpha && self.srs[0].table.alpha_width() >= p.width {
                        0
                    } else {
                        required.table_entries
                    }
                }
                None => 0,
            },
            _ => panic!("invalid commitment table section"),
        }
    }
    /// Whether this section's preparation policy selects embedding.
    /// `section` is in `0..SECTIONS`, in the order described by [`Config`].
    /// An embedded section can still have zero entries (for example, when
    /// folding reuses α layers); absent optional sections return `false`.
    ///
    /// # Panics
    ///
    /// Panics if `section >= SECTIONS`. Widths and byte ceilings are not checked.
    pub const fn embeds(self, section: usize) -> bool {
        let p = match section {
            SRS_START..=SRS_END => self.srs[section].preparation,
            FIXED_START..=FIXED_END => self.fixed[section - FIXED_START].preparation,
            SPARSE_START..=SPARSE_END => match self.sparse {
                Some(p) => p.preparation,
                None => return false,
            },
            FOLDING_SECTION => match self.folding {
                Some(p) => p.preparation,
                None => return false,
            },
            _ => panic!("invalid commitment table section"),
        };
        matches!(p, Preparation::Embed)
    }
    /// Prefix offset in the concatenated embedded affine artifact.
    ///
    /// Counts affine entries, not bytes, in all embedded sections before
    /// `section`. The range is `0..=SECTIONS`: `offset(SECTIONS)` is the valid
    /// end sentinel, equal to [`Self::embedded_entries`].
    ///
    /// # Panics
    ///
    /// Panics if `section > SECTIONS` or [`Self::entries`] panics for a preceding
    /// embedded section. Byte ceilings are not checked.
    pub const fn offset(self, section: usize) -> usize {
        assert!(section <= SECTIONS);
        let mut count = 0;
        let mut i = 0;
        while i < section {
            if self.embeds(i) {
                count += self.entries(i);
            }
            i += 1;
        }
        count
    }
    /// Affine artifact entry count.
    ///
    /// # Panics
    ///
    /// Panics under the conditions of [`Self::offset`] at `SECTIONS`.
    pub const fn embedded_entries(self) -> usize {
        self.offset(SECTIONS)
    }
    /// Cached expansion bytes plus one codebook per distinct α width.
    /// Original SRS caches and scratch are separate from this retained budget.
    ///
    /// # Panics
    ///
    /// Panics if any fixed or configured sparse/folding width is outside
    /// `2..=8`. Byte ceilings are not checked.
    pub const fn retained_bytes(self) -> usize {
        let mut bytes = 0;
        let mut i = 0;
        while i < SECTIONS {
            bytes += self.entries(i) * PREPARED_AFFINE_ENTRY_BYTES;
            i += 1;
        }
        let a = self.srs[0].table.alpha_width();
        let b = self.srs[1].table.alpha_width();
        if a != 0 {
            bytes += (1 << (2 * a)) * ALPHA_CODE_BYTES + (1 << (a - 1)) * ALPHA_COEFFICIENT_BYTES;
        }
        if b != 0 && b != a {
            bytes += (1 << (2 * b)) * ALPHA_CODE_BYTES + (1 << (b - 1)) * ALPHA_COEFFICIENT_BYTES;
        }
        bytes
    }
    /// Rejects invalid widths and memory overcommit; never changes the policy.
    /// This assertion-based check returns no error and never downgrades a table.
    ///
    /// # Panics
    ///
    /// Panics if either SRS expansion exceeds its bank's `max_bytes`, any fixed
    /// or configured sparse/folding width is outside `2..=8`, or the aggregate
    /// [`Self::retained_bytes`] exceeds `self.max_bytes`.
    pub const fn validate(self) {
        assert!(
            self.srs[0].table.entries() * PREPARED_AFFINE_ENTRY_BYTES <= self.srs[0].max_bytes,
            "coefficient table memory limit"
        );
        assert!(
            self.srs[1].table.entries() * PREPARED_AFFINE_ENTRY_BYTES <= self.srs[1].max_bytes,
            "Lagrange table memory limit"
        );
        assert!(
            self.retained_bytes() <= self.max_bytes,
            "commitment table memory limit"
        );
    }
}
/// Conservative policy for standalone artifact generation.
pub const DEFAULT: Config = Config {
    srs: [
        BankPolicy {
            table: SrsTable::Compact,
            preparation: Preparation::WarmUp,
            max_bytes: 16 << 20,
        },
        BankPolicy {
            table: SrsTable::None,
            preparation: Preparation::WarmUp,
            max_bytes: 16 << 20,
        },
    ],
    fixed: [FixedPolicy {
        width: 4,
        preparation: Preparation::WarmUp,
    }; 4],
    sparse: None,
    folding: None,
    max_bytes: 32 << 20,
};

/// Owned α residue data. Share one owner for all banks using its width.
pub struct Codebook {
    description: AlphaDescription,
    codes: Vec<u32>,
    coefficients: Vec<AlphaCoefficient>,
}
impl Codebook {
    /// Builds deterministic residue and integration data with bounded scratch.
    /// `width` must be in `5..=7` and match every α bank using this codebook.
    ///
    /// # Panics
    ///
    /// Panics if `width` is outside `5..=7`.
    pub fn new(width: u8) -> Self {
        let description = AlphaDescription::new(width).expect("α width");
        let mut codes = vec![0; description.codes()];
        let mut coefficients = vec![AlphaCoefficient::ZERO; description.layers()];
        let mut scratch = vec![0; description.codebook_scratch()];
        AlphaCodebook::prepare(description, &mut codes, &mut coefficients, &mut scratch);
        Self {
            description,
            codes,
            coefficients,
        }
    }
    /// Borrows the prepared data without copying it.
    pub fn view(&self) -> AlphaCodebook<'_> {
        AlphaCodebook::bind(self.description, &self.codes, &self.coefficients)
    }
}
/// Generates one fixed table, batching all normalization into one inversion.
///
/// Requires `policy.width` in `2..=8` and a valid nonidentity `base` satisfying
/// [`VestaAffine`]'s invariants. Callable without [`Config::validate`];
/// `policy.preparation` does not affect construction.
///
/// # Panics
///
/// Panics if `policy.width` is outside `2..=8`.
pub fn fixed<E: CurveTableEntry<Vesta>>(base: &VestaAffine, policy: FixedPolicy) -> Vec<E> {
    let count = policy.entries();
    let mut entries = vec![E::from_affine(base); count];
    FixedBaseTable::prepare_with(
        FixedBaseDescription {
            window_bits: policy.width,
        },
        base,
        &mut entries,
        &mut vec![VestaProjective::IDENTITY; count],
        &mut vec![Fq::ZERO; count],
    )
    .expect("fixed generator description");
    entries
}
/// Generates one SRS table in the requested entry representation.
/// Scratch is released before returning; α normalization uses one SRS layer.
///
/// Requires exactly [`N`] bases, including for [`SrsTable::None`]. Expanded
/// bases must satisfy [`VestaAffine`]'s valid nonidentity point invariants.
/// An α table requires `Some` codebook built with the table's
/// [`SrsTable::alpha_width`]; other table kinds ignore `codebook`.
/// No [`Config`] byte ceiling is checked here.
///
/// # Panics
///
/// Panics if `bases.len() != N`, an α codebook is absent or has the wrong width,
/// or the table/scratch dimensions exceed representable slice limits.
pub fn srs<E: CurveTableEntry<Vesta>>(
    bases: &[VestaAffine],
    table: SrsTable,
    codebook: Option<&Codebook>,
) -> Vec<E> {
    assert_eq!(bases.len(), N);
    let requirements = table.requirements::<E>();
    let mut entries = vec![E::from_affine(&VestaAffine::GENERATOR); requirements.table_entries];
    match table {
        SrsTable::None => {}
        SrsTable::Compact => {
            EisensteinTableBatch::prepare(
                bases,
                &mut entries,
                &mut vec![VestaProjective::IDENTITY; requirements.projective_scratch],
                &mut vec![Fq::ZERO; requirements.field_scratch],
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
        }
        _ => {
            let book = codebook.expect("shared α codebook").view();
            assert_eq!(book.description().window_bits(), table.alpha_width());
            AlphaTable::prepare(
                book,
                bases,
                &mut entries,
                &mut vec![VestaProjective::IDENTITY; requirements.projective_scratch],
                &mut vec![Fq::ZERO; requirements.field_scratch],
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
        }
    }
    entries
}
/// Repeated-coordinate row range, shared by the host and prover.
pub fn repeated_coordinate_rows() -> core::ops::Range<usize> {
    let start = crate::regions::REGION_STARTS[297];
    start + 2..start + 128
}
/// Derives H directly from the Lagrange SRS.
///
/// `lagrange` must cover [`repeated_coordinate_rows`] and contain valid
/// [`VestaAffine`] points. The sum over those rows must be nonidentity; the
/// slice need not have exactly [`N`] entries.
///
/// # Panics
///
/// Panics if the slice does not cover the row range or its sum is the identity.
pub fn repeated_coordinate_base(lagrange: &[VestaAffine]) -> VestaAffine {
    let sum = lagrange[repeated_coordinate_rows()]
        .iter()
        .fold(VestaProjective::IDENTITY, |sum, base| sum.add_mixed(base));
    *sum.to_point()
        .as_affine()
        .expect("nonidentity repeated-coordinate base")
}

/// Generates a separate layer-major odd bank when α layers cannot be reused.
///
/// Requires `width` in `2..=8` and valid nonidentity bases satisfying
/// [`VestaAffine`]'s invariants. Any base count, including zero, is allowed if
/// the table and scratch sizes fit representable slices as determined by
/// [`OddTable::requirements`]. Callable without [`Config::validate`]; no
/// [`Config`] byte ceiling is checked here.
///
/// # Panics
///
/// Panics if `width` is outside `2..=8` or the required dimensions exceed
/// representable slice limits.
pub fn odd<E: CurveTableEntry<Vesta>>(bases: &[VestaAffine], width: u8) -> Vec<E> {
    let requirements = OddTable::<Vesta, E>::requirements(width, bases.len())
        .expect("validated folding table dimensions");
    let mut entries = vec![E::from_affine(&VestaAffine::GENERATOR); requirements.table_entries];
    OddTable::prepare(
        width,
        bases,
        &mut entries,
        &mut vec![VestaProjective::IDENTITY; requirements.projective_scratch],
        &mut vec![Fq::ZERO; requirements.field_scratch],
        TaskBudget::SERIAL,
        &SerialExecutor,
    )
    .expect("validated folding table dimensions");
    entries
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::size_of;
    use udon::curve::PreparedAffinePoint;

    #[test]
    fn payload_inventory_and_shared_codebooks() {
        assert_eq!(size_of::<VestaAffine>(), 64);
        assert_eq!(size_of::<PreparedAffinePoint<Vesta>>(), 96);
        assert_eq!(size_of::<AlphaCoefficient>(), 12);
        assert_eq!(
            size_of::<crate::PreparedPointsFile>(),
            (3 * N + crate::fixed_columns::SINSEMILLA_TABLE_ROWS + 2) * 64
        );
        let fixed: usize = DEFAULT.fixed.iter().map(|p| p.entries() * 96).sum();
        assert_eq!(DEFAULT.retained_bytes(), 8 * N * 96 + fixed);
        assert_eq!(DEFAULT.embedded_entries(), 0);
        for table in [SrsTable::Alpha5, SrsTable::Alpha6, SrsTable::Alpha7] {
            let mut config = DEFAULT;
            for policy in &mut config.srs {
                policy.table = table;
                policy.preparation = Preparation::Embed;
            }
            config.folding = Some(FoldingPolicy {
                width: table.alpha_width(),
                reuse_alpha: true,
                preparation: Preparation::Embed,
            });
            config.validate();
            let desc = AlphaDescription::new(table.alpha_width()).unwrap();
            let book =
                desc.codes() * size_of::<u32>() + desc.layers() * size_of::<AlphaCoefficient>();
            assert_eq!(
                config.retained_bytes(),
                2 * table.entries() * 96 + fixed + book
            );
            assert_eq!(config.entries(17), 0);
            assert_eq!(config.embedded_entries() * 64, 2 * table.entries() * 64);
            config.folding.as_mut().unwrap().reuse_alpha = false;
            assert_eq!(config.entries(17), N * (1 << (table.alpha_width() - 2)));
            assert_eq!(config.offset(17), 2 * table.entries());
            assert_eq!(
                config.offset(SECTIONS),
                config.offset(17) + config.entries(17)
            );
        }
    }

    #[test]
    #[should_panic(expected = "coefficient table memory limit")]
    fn bank_ceiling_rejects_instead_of_downgrading() {
        let mut config = DEFAULT;
        config.srs[0].table = SrsTable::Alpha7;
        config.srs[0].max_bytes = config.srs[0].table.entries() * 96 - 1;
        config.validate();
    }

    #[test]
    #[should_panic(expected = "commitment table memory limit")]
    fn aggregate_ceiling_includes_the_codebook() {
        let mut config = DEFAULT;
        config.srs[0].table = SrsTable::Alpha5;
        config.max_bytes = config.retained_bytes() - 1;
        config.validate();
    }
}
