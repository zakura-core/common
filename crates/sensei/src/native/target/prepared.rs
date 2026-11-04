//! Prepared rows and polynomial columns, borrowing artifacts or owning transforms.
//!
//! The caller selects storage policy; these containers preserve dimensions and
//! expose the same coefficient and residue-major coset views in either form.

use alloc::vec::Vec;

use crate::native::field::Fp;
use crate::native::generated_expressions::PREPARED_GATE_SELECTOR_ROW;
use crate::native::polynomial::{CosetTiles, FpCosetView};
#[cfg(test)]
use crate::native::polynomial::{coset_fft_with_nonzero_prefix, ifft};
use sensei_shared::{EXTENDED_N, N};

use super::{CosetColumns, TargetError};

/// Prepared row-shaped storage either borrowed from an embedded artifact or
/// derived at load — equal field values either way, selected by the
/// artifact's `embed_*` dial. One store for every fixed-width row matrix the
/// target prepares (coefficient columns, gate-selector rows, instance-basis
/// rows); the physical layout is the row type's, contiguous in both forms.
///
/// Both constructors validate the row count, so a consumer indexing `rows()`
/// by a circuit dimension cannot go out of bounds; the values themselves are
/// pinned by the canonical-content digest tests.
pub(crate) enum PreparedRows<Row: 'static> {
    Embedded(&'static [Row]),
    Derived(Vec<Row>),
}

impl<Row: 'static> PreparedRows<Row> {
    /// Borrows an embedded artifact of exactly `expected` rows.
    #[allow(dead_code)] // reached only by the artifacts whose dials are on
    pub(super) fn embedded(rows: &'static [Row], expected: usize) -> Result<Self, TargetError> {
        (rows.len() == expected)
            .then_some(Self::Embedded(rows))
            .ok_or(TargetError::Dimension)
    }

    /// Owns rows derived at load, exactly `expected` of them.
    #[allow(dead_code)] // reached only by the artifacts whose dials are off
    pub(super) fn derived(rows: Vec<Row>, expected: usize) -> Result<Self, TargetError> {
        (rows.len() == expected)
            .then_some(Self::Derived(rows))
            .ok_or(TargetError::Dimension)
    }

    /// The rows, whichever form holds them.
    pub(super) fn rows(&self) -> &[Row] {
        match self {
            Self::Embedded(rows) => rows,
            Self::Derived(rows) => rows,
        }
    }
}

/// Coefficient columns, interpolated at load or embedded (the
/// `embed_fixed_coefficients` / `embed_sigma_coefficients` dials).
pub(crate) type CoefficientColumns = PreparedRows<[Fp; N]>;

/// Interpolates Lagrange columns into coefficient arrays: the load-time
/// alternative to an embedded coefficient artifact, producing the same values
/// the generator bakes (pinned by the canonical-content digest test).
#[cfg_attr(
    all(embed_fixed_coefficients, embed_sigma_coefficients),
    allow(dead_code)
)]
pub(super) fn derive_coefficient_columns(
    values: &[[Fp; N]],
    fft: &crate::native::polynomial::PreparedFft,
) -> Result<Vec<[Fp; N]>, TargetError> {
    (values.iter().collect::<Vec<_>>())
        .into_iter()
        .map(|column: &[Fp; N]| {
            let mut coefficients = *column;
            if !fft.ifft(&mut coefficients) {
                return Err(TargetError::Dimension);
            }
            Ok(coefficients)
        })
        .collect::<Vec<_>>()
        .into_iter()
        .collect()
}

impl CosetColumns {
    fn residue_major(columns: Vec<crate::native::buffer::Buffer<Fp>>) -> Result<Self, TargetError> {
        if columns.iter().any(|column| column.len() != EXTENDED_N) {
            return Err(TargetError::Dimension);
        }
        Ok(Self::Derived(columns))
    }

    pub(crate) fn len(&self) -> usize {
        match self {
            Self::Derived(columns) => columns.len(),
            #[cfg(any(embed_fixed_cosets, embed_sigma_cosets))]
            Self::Embedded(columns) => columns.len(),
        }
    }

    pub(crate) fn column(&self, index: usize) -> FpCosetView<'_> {
        let values: &[Fp] = match self {
            Self::Derived(columns) => &columns[index],
            #[cfg(any(embed_fixed_cosets, embed_sigma_cosets))]
            Self::Embedded(columns) => &columns[index],
        };
        FpCosetView::from_flat(values)
            .unwrap_or_else(|| unreachable!("coset columns have the extended length"))
    }

    /// Allocates small views once per quotient fold; column payloads stay shared.
    #[cfg(test)]
    pub(crate) fn collect_views(&self) -> Vec<FpCosetView<'_>> {
        (0..self.len()).map(|index| self.column(index)).collect()
    }
}

/// The prepared gate-selector matrix, one row per extended-coset row,
/// embedded or filled at load (the `embed_gate_selectors` dial).
pub(crate) type GateSelectorRows = PreparedRows<[Fp; PREPARED_GATE_SELECTOR_ROW]>;

pub(crate) struct PreparedPolynomials {
    coefficients: CoefficientColumns,
    cosets: CosetColumns,
}

/// Coefficient and coset column matrices recomputed by the test oracle.
#[cfg(test)]
type DerivedPolynomialForms = (Vec<Vec<Fp>>, Vec<Vec<Fp>>);

impl PreparedPolynomials {
    /// Retains coefficients and prepares matching residue-major cosets.
    /// Warmup expands into heap storage; embedded cosets are borrowed in place.
    /// Across fixed and sigma columns this trades 22 MiB of artifact payload
    /// against 44 runtime expansions and 22 MiB of retained heap. Coefficient
    /// storage is selected independently by the caller.
    pub(super) fn prepare(
        coefficients: CoefficientColumns,
        embedded_cosets: Option<&'static [[Fp; EXTENDED_N]]>,
        fft: &crate::native::polynomial::PreparedFft,
        execution: crate::native::worker::Execution<'_>,
    ) -> Result<Self, TargetError> {
        let cosets = match embedded_cosets {
            #[cfg(any(embed_fixed_cosets, embed_sigma_cosets))]
            Some(cosets) => CosetColumns::Embedded(cosets),
            #[cfg(not(any(embed_fixed_cosets, embed_sigma_cosets)))]
            Some(_) => return Err(TargetError::Dimension),
            None => CosetColumns::residue_major(
                execution
                    .map(coefficients.rows().iter(), |column, execution| {
                        fft.coefficients::<8>(column, execution)
                            .map(CosetTiles::into_flat)
                            .ok_or(TargetError::Dimension)
                    })
                    .into_iter()
                    .collect::<Result<Vec<_>, _>>()?,
            )?,
        };
        if cosets.len() != coefficients.rows().len() {
            return Err(TargetError::Dimension);
        }
        Ok(Self {
            coefficients,
            cosets,
        })
    }

    /// Recomputes coefficient and coset columns from Lagrange evaluation
    /// forms, as the cross-check oracle for the embedded coefficients.
    #[cfg(test)]
    pub(super) fn derive(
        values: &[[Fp; N]],
        expected_columns: usize,
    ) -> Result<DerivedPolynomialForms, TargetError> {
        if values.len() != expected_columns {
            return Err(TargetError::Dimension);
        }

        let mut coefficients = Vec::with_capacity(expected_columns);
        let mut cosets = Vec::with_capacity(expected_columns);
        for values in values {
            let mut column_coefficients = values.to_vec();
            if !ifft(&mut column_coefficients) {
                return Err(TargetError::Dimension);
            }
            let mut column_coset = column_coefficients.clone();
            column_coset.resize_with(EXTENDED_N, || <Fp>::ZERO);
            if !coset_fft_with_nonzero_prefix(&mut column_coset, N) {
                return Err(TargetError::Dimension);
            }
            coefficients.push(column_coefficients);
            cosets.push(column_coset);
        }
        Ok((coefficients, cosets))
    }

    pub(crate) fn coefficients(&self) -> &[[Fp; N]] {
        self.coefficients.rows()
    }

    pub(crate) fn cosets(&self) -> &CosetColumns {
        &self.cosets
    }
}
