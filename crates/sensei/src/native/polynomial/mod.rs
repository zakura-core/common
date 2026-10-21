//! Circuit polynomial ownership over Udon's polynomial operations and FFT plans.
//!
//! Coset ownership and row-indexed views come first, followed by prepared
//! transform tables, reusable workspace, and unprepared expansion adapters.
//! These owners stay together so transforms can borrow coset storage without
//! exposing its fields. Test-only transform and division references live in
//! `reference.rs`, with their existing caller paths retained here.
use super::buffer::{Buffer, BufferPool};
use alloc::sync::Arc;
use alloc::{vec, vec::Vec};
use core::ops::Index;
use udon::{
    exec::{
        ExecutionOptions, SerialExecutor,
        execution::{Identity, TaskStorage},
    },
    fft::{Domain, Expansion, ExpansionScaleNormalization, ExpansionScales, Transform},
    field::{Fp, PallasBase, PastaField, PrimeModulus},
};

#[cfg(test)]
use udon::fft::ResidueLayout;
#[cfg(test)]
pub(crate) use udon::polynomial::evaluate;

pub(crate) type SharedPoly = super::storage::Column<Fp>;
const BASE_LOG_SIZE: u32 = sensei_shared::K;
const EXTENDED_LOG_SIZE: u32 = sensei_shared::EXTENDED_K;
const EXTENDED_TILE_LEN: usize = 1 << BASE_LOG_SIZE;
const EXTENDED_TILE_COUNT: usize = 1 << (EXTENDED_LOG_SIZE - BASE_LOG_SIZE);
const CLASS_2N_TILE_COUNT: usize = 2;

/// Shares residue-major evaluations addressed by natural extended-domain rows.
///
/// Let `N = EXTENDED_TILE_LEN`, `R = EXTENDED_TILE_COUNT` (currently 8), and
/// `stride = R / TILES`; the supported degree classes have 1, 2, 4, or 8 tiles.
/// Every index is a row of the full `R*N` domain, including for smaller classes:
/// it must be below `R*N` and divisible by `stride`. Its class residue is
/// `t = row / stride % TILES`, its tile-local index is `k = row / R`, and
/// [`coset_index`] maps it to element `t*N + k` of the complete class buffer.
/// This is Udon's [`ResidueLayout::index_at_extended_row`](udon::fft::ResidueLayout::index_at_extended_row)
/// mapping for the class domain.
///
/// The same fields represent three states, without a separate state tag:
///
/// | Constructed by | `values.len()` | `start` | Valid natural extended-row indices |
/// | --- | --- | --- | --- |
/// | [`pending`](Self::pending) | 0 | 0 | None; a placeholder that consumers must not read |
/// | [`from_flat`](Self::from_flat) | `TILES*N` | 0 | Every class row described above |
/// | [`from_residue(t, ...)`](Self::from_residue) | `N` | `t*N` | Only `stride*t + R*k` for `0 <= k < N` |
///
/// `start` measures elements in the complete residue-major buffer. Indexing
/// subtracts it from `t*N + k` to address the stored slice. [`CosetView`] preserves
/// this state and mapping; it does not make a pending or partial value complete.
/// Cloning shares the backing storage; recovering it requires the shape and
/// ownership conditions of [`into_flat`](Self::into_flat).
///
/// For a small example, take `N = 4`, `R = 8`, and write `v_r` for natural
/// row `r`. Natural order is `v_0, v_1, ..., v_31`; the complete eight-tile
/// buffer instead starts `v_0, v_8, v_16, v_24, v_1, v_9, v_17, v_25, ...`.
/// Residue 3 alone stores `v_3, v_11, v_19, v_27` with `start = 12`.
/// Indexing row 19 maps to complete-buffer element 14, hence local element 2.
/// A [base-row rotation](super::evaluation::rotated_extended_row) adds 8 modulo
/// 32: rows `19 -> 27 -> 3` stay in this residue, moving local indices
/// `2 -> 3 -> 0`. Negative rotations wrap in the same tile too.
///
/// The smaller 4N, 2N, and N classes select extended rows divisible by 2, 4,
/// and 8 respectively. In the example, `TILES = 2` stores
/// `v_0, v_8, v_16, v_24, v_4, v_12, v_20, v_28`. Its row 12 is element 5
/// of the complete buffer, or local element 1 of residue 1 (`start = 4`). The
/// index argument remains 12; both the class's natural-row index 3 and local
/// index 1 are invalid extended-row arguments. Rotating row 12 by one base
/// row still adds 8, reaching row 20 in the same tile.
///
/// The [artifact coset encoder](../../../zakura_sensei_artifacts/polynomials/cosets/fn.coset_bytes.html)
/// serializes the full class in this same residue-major order.
pub(crate) struct CosetTiles<M: PrimeModulus, const TILES: usize> {
    values: super::storage::Column<PastaField<M>>,
    start: usize,
}
impl<M: PrimeModulus, const TILES: usize> Clone for CosetTiles<M, TILES> {
    fn clone(&self) -> Self {
        Self {
            values: self.values.clone(),
            start: self.start,
        }
    }
}
impl<M: PrimeModulus, const TILES: usize> CosetTiles<M, TILES> {
    pub(crate) fn pending() -> Self {
        Self {
            values: super::storage::Column::default(),
            start: 0,
        }
    }
    pub(crate) fn from_flat(values: impl Into<Buffer<PastaField<M>>>) -> Option<Self> {
        let values = values.into();
        (values.len() == TILES * EXTENDED_TILE_LEN).then(|| Self {
            values: super::storage::Column::new(values),
            start: 0,
        })
    }
    /// One completed class residue, shared with consumers of its rotation-closed
    /// rows; see [`CosetTiles`] for the residue-to-extended-row mapping.
    pub(crate) fn from_residue(residue: usize, values: Arc<Buffer<PastaField<M>>>) -> Option<Self> {
        (residue < TILES && values.len() == EXTENDED_TILE_LEN).then(|| Self {
            values: values.into(),
            start: residue * EXTENDED_TILE_LEN,
        })
    }
    #[cfg(test)]
    pub(crate) fn from_row_chunks(
        chunks: impl IntoIterator<Item = Vec<PastaField<M>>>,
    ) -> Option<Self> {
        Self::from_flat(chunks.into_iter().flatten().collect::<Vec<_>>())
    }
    #[cfg(test)]
    pub(crate) fn from_dense_rows(values: &[PastaField<M>]) -> Option<Self> {
        if values.len() != TILES * EXTENDED_TILE_LEN {
            return None;
        }
        let mut flat = vec![PastaField::ZERO; TILES * EXTENDED_TILE_LEN];
        ResidueLayout::new(flat.len(), TILES)
            .ok()?
            .copy_from_natural(values, &mut flat);
        Self::from_flat(flat)
    }
    /// Recovers the complete buffer in residue-major order, without reordering.
    ///
    /// Panics unless the length is `TILES * EXTENDED_TILE_LEN` and this is the
    /// last owner of the backing allocation. Drop other clones and any supplied
    /// `Arc` owners first. A single residue has complete shape only for `TILES = 1`.
    pub(crate) fn into_flat(self) -> Buffer<PastaField<M>> {
        assert_eq!(self.values.len(), TILES * EXTENDED_TILE_LEN);
        self.values.into_unique().expect("last coset owner")
    }
    #[cfg(test)]
    pub(crate) fn to_dense_rows(&self) -> Vec<PastaField<M>> {
        let mut result = vec![PastaField::ZERO; self.values.len()];
        ResidueLayout::new(self.values.len(), TILES)
            .unwrap()
            .copy_to_natural(&self.values, &mut result);
        result
    }
    #[cfg(test)]
    pub(crate) fn iter(&self) -> core::slice::Iter<'_, PastaField<M>> {
        self.values.iter()
    }
    pub(crate) fn view(&self) -> CosetView<'_, M, TILES> {
        CosetView {
            values: &self.values,
            start: self.start,
        }
    }
}
impl<M: PrimeModulus, const TILES: usize> Index<usize> for CosetTiles<M, TILES> {
    type Output = PastaField<M>;
    fn index(&self, row: usize) -> &Self::Output {
        &self.values[coset_index::<TILES>(row) - self.start]
    }
}
/// Borrows the state and extended-row indexing contract of [`CosetTiles`].
/// [`from_flat`](Self::from_flat) borrows a complete class; [`CosetTiles::view`]
/// can also borrow a pending or single-residue value.
pub(crate) struct CosetView<'a, M: PrimeModulus, const TILES: usize> {
    values: &'a [PastaField<M>],
    start: usize,
}
impl<M: PrimeModulus, const TILES: usize> Clone for CosetView<'_, M, TILES> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<M: PrimeModulus, const TILES: usize> Copy for CosetView<'_, M, TILES> {}
impl<'a, M: PrimeModulus, const TILES: usize> CosetView<'a, M, TILES> {
    pub(crate) fn from_flat(values: &'a [PastaField<M>]) -> Option<Self> {
        if values.len() != TILES * EXTENDED_TILE_LEN {
            return None;
        }
        Some(Self { values, start: 0 })
    }
    pub(crate) fn at_extended_row(&self, row: usize) -> PastaField<M> {
        self[row]
    }
}
impl<M: PrimeModulus, const TILES: usize> Index<usize> for CosetView<'_, M, TILES> {
    type Output = PastaField<M>;
    fn index(&self, row: usize) -> &Self::Output {
        &self.values[coset_index::<TILES>(row) - self.start]
    }
}
#[inline(always)]
fn coset_index<const TILES: usize>(row: usize) -> usize {
    let stride = EXTENDED_TILE_COUNT / TILES;
    assert!(row < EXTENDED_TILE_COUNT * EXTENDED_TILE_LEN && row.is_multiple_of(stride));
    (row / stride % TILES) * EXTENDED_TILE_LEN + row / EXTENDED_TILE_COUNT
}
pub(crate) type ExtendedCosetTiles<M> = CosetTiles<M, EXTENDED_TILE_COUNT>;
pub(crate) type ExtendedCosetView<'a, M> = CosetView<'a, M, EXTENDED_TILE_COUNT>;
pub(crate) type FpCosetTiles = ExtendedCosetTiles<PallasBase>;
pub(crate) type FpCosetView<'a> = ExtendedCosetView<'a, PallasBase>;
pub(crate) type FpClass2NTiles = CosetTiles<PallasBase, CLASS_2N_TILE_COUNT>;
pub(crate) type FpClass2NView<'a> = CosetView<'a, PallasBase, CLASS_2N_TILE_COUNT>;

// Immutable transform tables borrowed directly from generated artifacts.
#[cfg(embed_fft_tables)]
crate::static_data::embed_array! {
    pub(crate) static FFT_TABLES: [Fp; sensei_shared::fft::TABLE_LEN] = artifact_path!(fft_tables);
}
#[cfg(embed_expansion_scales)]
crate::static_data::embed_array! {
    pub(crate) static EXPANSION_SCALES: [Fp; sensei_shared::fft::SCALE_LEN] = artifact_path!(expansion_scales);
}

/// Optional tables never allocate in the on-demand or embedded modes.
enum TableValues {
    Absent,
    Owned(Vec<Fp>),
    #[cfg(any(embed_fft_tables, embed_expansion_scales))]
    Embedded(&'static [Fp]),
}
impl TableValues {
    fn values(&self) -> Option<&[Fp]> {
        match self {
            Self::Absent => None,
            Self::Owned(values) => Some(values),
            #[cfg(any(embed_fft_tables, embed_expansion_scales))]
            Self::Embedded(values) => Some(values),
        }
    }
}

pub(crate) struct PreparedFft {
    base: FftTables,
    cosets: [FftTables; 4],
    residue_scales: [TableValues; 4],
}
struct FftTables {
    domain: udon::fft::CosetDomain<PallasBase>,
    values: TableValues,
}
impl FftTables {
    fn new(plan_index: usize) -> Self {
        use crate::tuning::{self, OptionalPreparation};
        use sensei_shared::fft as layout;
        let domain = Domain::for_size(layout::plan_size(plan_index)).unwrap();
        let domain = if plan_index == 0 {
            domain.subgroup()
        } else {
            domain.coset()
        };
        let values = match tuning::FFT_TABLES {
            OptionalPreparation::OnDemand => TableValues::Absent,
            OptionalPreparation::WarmUp => {
                use udon::fft::TablesMut;
                let len = domain.size() / 2;
                let mut values = vec![<Fp>::ZERO; 3 * len];
                let (forward, rest) = values.split_at_mut(len);
                let (inverse, finish) = rest.split_at_mut(len);
                TablesMut {
                    forward: Some(forward),
                    inverse: Some(inverse),
                    inverse_finish: Some(finish),
                }
                .prepare(domain);
                TableValues::Owned(values)
            }
            OptionalPreparation::Embed => {
                #[cfg(embed_fft_tables)]
                {
                    let start = layout::table_offset(plan_index);
                    TableValues::Embedded(&FFT_TABLES[start..start + 3 * domain.size() / 2])
                }
                #[cfg(not(embed_fft_tables))]
                unreachable!("build and runtime share the FFT embedding policy")
            }
        };
        Self { domain, values }
    }
    fn plan(&self) -> Transform<'_, PallasBase> {
        use udon::fft::Tables;
        let len = self.domain.size() / 2;
        let values = self.values.values();
        Tables {
            forward: values.map(|values| &values[..len]),
            inverse: values.map(|values| &values[len..2 * len]),
            inverse_finish: values.map(|values| &values[2 * len..]),
        }
        .bind(self.domain)
    }
}
impl PreparedFft {
    pub(crate) fn new() -> Self {
        use crate::tuning::{self, OptionalPreparation};
        Self {
            base: FftTables::new(0),
            residue_scales: core::array::from_fn(|coset_index| match tuning::EXPANSION_SCALES {
                OptionalPreparation::OnDemand => TableValues::Absent,
                OptionalPreparation::WarmUp => {
                    let domain = Domain::new(BASE_LOG_SIZE + coset_index as u32)
                        .unwrap()
                        .coset();
                    let mut scales = vec![<Fp>::ZERO; domain.size()];
                    ExpansionScales::prepare(
                        EXTENDED_TILE_LEN,
                        domain,
                        ExpansionScaleNormalization::Coefficients,
                        &mut scales,
                    )
                    .unwrap();
                    TableValues::Owned(scales)
                }
                OptionalPreparation::Embed => {
                    #[cfg(embed_expansion_scales)]
                    {
                        let start = sensei_shared::fft::scale_offset(coset_index);
                        TableValues::Embedded(
                            &EXPANSION_SCALES[start..start + (EXTENDED_TILE_LEN << coset_index)],
                        )
                    }
                    #[cfg(not(embed_expansion_scales))]
                    unreachable!("build and runtime share the expansion embedding policy")
                }
            }),
            // Plan 0 is the base subgroup; coset slots start at plan 1.
            cosets: core::array::from_fn(|coset_index| FftTables::new(coset_index + 1)),
        }
    }
    pub(crate) fn expansion(&self, tiles: usize) -> Option<Expansion<'_, PallasBase>> {
        if !tiles.is_power_of_two() {
            return None;
        }
        let coset_index = tiles.trailing_zeros() as usize;
        let domain = self.cosets.get(coset_index)?.domain;
        let scales = self.residue_scales[coset_index]
            .values()
            .map(|values| {
                ExpansionScales::bind(
                    EXTENDED_TILE_LEN,
                    domain,
                    ExpansionScaleNormalization::Coefficients,
                    values,
                )
            })
            .transpose()
            .ok()?;
        Expansion::new(self.base.plan(), domain, scales).ok()
    }
    pub(crate) fn class_plan(&self, log: usize) -> Transform<'_, PallasBase> {
        self.cosets[log].plan()
    }
    pub(crate) fn ifft(&self, values: &mut [Fp]) -> bool {
        self.base
            .plan()
            .inverse(
                values,
                ExecutionOptions::default(),
                &SerialExecutor,
                &mut [],
            )
            .is_ok()
    }
    pub(crate) fn coefficients<const TILES: usize>(
        &self,
        values: &[Fp],
        execution: super::worker::Execution<'_>,
    ) -> Option<CosetTiles<PallasBase, TILES>> {
        let expansion = self.expansion(TILES)?;
        let mut output = execution.buffer(TILES * EXTENDED_TILE_LEN, false);
        let options = ExecutionOptions::default().with_task_budget(execution.budget);
        expansion
            .coefficients(values, &mut output, options, &execution, &mut [])
            .ok()?;
        CosetTiles::from_flat(output)
    }
    pub(crate) fn short_product(
        &self,
        values: &[Fp],
        factor: &FpCosetTiles,
        execution: super::worker::Execution<'_>,
    ) -> Option<FpCosetTiles> {
        let expansion = self.expansion(EXTENDED_TILE_COUNT)?;
        let mut output = execution.buffer(factor.values.len(), false);
        let options = ExecutionOptions::default().with_task_budget(execution.budget);
        expansion
            .short_product(
                values,
                expansion.view(&factor.values),
                &mut output,
                options,
                &execution,
                &mut [],
            )
            .ok()?;
        CosetTiles::from_flat(output)
    }
}
/// Reusable frontier metadata and bounded quotient field banks.
// Full-N expansion tasks need one slot. Class inverses can expose all eight
// fragments and their lift additions under the same bounded driver.
pub(crate) const FFT_FRONTIER: usize = 16;
pub(crate) struct FftWorkspace {
    pub(crate) buffers: BufferPool<Fp>,
    pub(crate) expansion_ids: Vec<[Identity; 1]>,
    pub(crate) expansion_storage: Vec<[[TaskStorage; FFT_FRONTIER]; 1]>,
    pub(crate) class_ids: [[Identity; 2]; 4],
    pub(crate) class_storage: [[[TaskStorage; FFT_FRONTIER]; 2]; 4],
    pub(crate) lookup_id: Identity,
    pub(crate) lookup_storage: [TaskStorage; FFT_FRONTIER],
}
impl Default for FftWorkspace {
    fn default() -> Self {
        Self::new(BufferPool::default())
    }
}
impl FftWorkspace {
    pub(crate) fn new(buffers: BufferPool<Fp>) -> Self {
        Self {
            buffers,
            expansion_ids: Vec::new(),
            expansion_storage: Vec::new(),
            class_ids: core::array::from_fn(|_| core::array::from_fn(|_| Identity::new())),
            class_storage: [const { [const { [const { TaskStorage::EMPTY }; FFT_FRONTIER] }; 2] };
                4],
            lookup_id: Identity::new(),
            lookup_storage: [const { TaskStorage::EMPTY }; FFT_FRONTIER],
        }
    }
}
impl FftWorkspace {
    pub(crate) fn provision(&mut self, columns: usize) {
        self.expansion_ids
            .resize_with(columns, || [Identity::new()]);
        self.expansion_storage.resize_with(columns, || {
            [[const { TaskStorage::EMPTY }; FFT_FRONTIER]; 1]
        });
    }
    #[cfg(test)]
    pub(crate) fn capacities(&self) -> Vec<usize> {
        let inventory = self.buffers.inventory();
        vec![
            self.expansion_ids.capacity(),
            self.expansion_storage.capacity(),
            inventory.allocations,
            inventory.buffers,
            inventory.bytes,
        ]
    }
    #[cfg(all(test, feature = "verifier"))]
    pub(crate) fn retained_bytes(&self) -> usize {
        self.expansion_ids.capacity() * size_of::<[Identity; 1]>()
            + self.expansion_storage.capacity() * size_of::<[[TaskStorage; FFT_FRONTIER]; 1]>()
            + size_of_val(&self.class_ids)
            + size_of_val(&self.class_storage)
            + size_of_val(&self.lookup_id)
            + size_of_val(&self.lookup_storage)
    }
}

fn plan<M: PrimeModulus>(size: usize, coset: bool) -> Option<Transform<'static, M>> {
    let domain = Domain::for_size(size).ok()?;
    Some(Transform::new(if coset {
        domain.coset()
    } else {
        domain.subgroup()
    }))
}
fn expansion<M: PrimeModulus>(tiles: usize) -> Option<Expansion<'static, M>> {
    Expansion::new(
        plan(EXTENDED_TILE_LEN, false)?,
        Domain::for_size(tiles * EXTENDED_TILE_LEN).ok()?.coset(),
        None,
    )
    .ok()
}
fn residue_transforms<M: PrimeModulus, const TILES: usize>(
    coefficients: &[PastaField<M>],
) -> Option<CosetTiles<M, TILES>> {
    if coefficients.len() != EXTENDED_TILE_LEN {
        return None;
    }
    let mut output = vec![PastaField::ZERO; TILES * EXTENDED_TILE_LEN];
    expansion(TILES)?
        .coefficients(
            coefficients,
            &mut output,
            ExecutionOptions::default(),
            &SerialExecutor,
            &mut [],
        )
        .ok()?;
    CosetTiles::from_flat(output)
}
pub(crate) fn base_coefficients_to_extended_coset_tiles<M: PrimeModulus>(
    coefficients: &[PastaField<M>],
) -> Option<ExtendedCosetTiles<M>> {
    residue_transforms(coefficients)
}
#[cfg(test)]
mod reference;
#[cfg(test)]
pub(crate) use reference::{
    base_coefficients_to_class_2n_coset_tiles, base_coefficients_to_extended_coset,
    base_lagrange_to_extended_coset, base_lagrange_to_extended_coset_tiles, coset_fft,
    coset_fft_with_nonzero_prefix, coset_ifft, fft, ifft, quotient_numerator_to_coefficients,
    short_coefficients_times_factor_coset_tiles, synthetic_division, synthetic_division_in_place,
};

#[cfg(test)]
mod tests;
