use super::circuit::{Any, Column};
use crate::{
    arithmetic::CurveAffine,
    poly::{Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial},
};

pub(crate) mod keygen;
pub(crate) mod prover;
pub(crate) mod verifier;

const PERMUTATION_PRODUCT_DEGREE_OVERHEAD: usize = 2;

fn permutation_chunk_len(cs_degree: usize) -> usize {
    assert!(cs_degree > PERMUTATION_PRODUCT_DEGREE_OVERHEAD);
    cs_degree - PERMUTATION_PRODUCT_DEGREE_OVERHEAD
}

/// A permutation argument.
#[derive(Debug, Clone)]
pub(crate) struct Argument {
    /// A sequence of columns involved in the argument.
    columns: Vec<Column<Any>>,
}

impl Argument {
    pub(crate) fn new() -> Self {
        Argument { columns: vec![] }
    }

    /// Returns the minimum circuit degree required by the permutation argument.
    /// The argument may use larger degree gates depending on the actual
    /// circuit's degree and how many columns are involved in the permutation.
    pub(crate) fn required_degree(&self) -> usize {
        // degree 2:
        // l_0(X) * (1 - z(X)) = 0
        //
        // We will fit as many polynomials p_i(X) as possible
        // into the required degree of the circuit, so the
        // following will not affect the required degree of
        // this middleware.
        //
        // (1 - (l_last(X) + l_blind(X))) * (
        //   z(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
        // - z(X) \prod (p(X) + \delta^i \beta X + \gamma)
        // )
        //
        // On the first sets of columns, except the first
        // set, we will do
        //
        // l_0(X) * (z(X) - z'(\omega^(last) X)) = 0
        //
        // where z'(X) is the permutation for the previous set
        // of columns.
        //
        // On the final set of columns, we will do
        //
        // degree 3:
        // l_last(X) * (z'(X)^2 - z'(X)) = 0
        //
        // which will allow the last value to be zero to
        // ensure the argument is perfectly complete.

        // There are constraints of degree 3 regardless of the
        // number of columns involved.
        3
    }

    pub(crate) fn add_column(&mut self, column: Column<Any>) {
        if !self.columns.contains(&column) {
            self.columns.push(column);
        }
    }

    pub(crate) fn get_columns(&self) -> Vec<Column<Any>> {
        self.columns.clone()
    }

    /// Returns the number of product-polynomial sets at the circuit degree.
    pub(super) fn set_count(&self, cs_degree: usize) -> usize {
        self.columns
            .chunks(permutation_chunk_len(cs_degree))
            .count()
    }
}

/// The verifying key for a single permutation argument.
#[derive(Clone, Debug)]
pub(crate) struct VerifyingKey<C: CurveAffine> {
    commitments: Vec<C>,
}

impl<C: CurveAffine> VerifyingKey<C> {
    /// The commitments to the permutation columns (one per column), for Lean fixture export.
    #[cfg(feature = "unstable-verifier-fingerprint")]
    pub(crate) fn commitments(&self) -> &[C] {
        &self.commitments
    }
}

/// The proving key for a single permutation argument.
#[derive(Clone, Debug)]
pub(crate) struct ProvingKey<C: CurveAffine> {
    permutations: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
    /// Whether each permutation column leaves every cell in place.
    identity_columns: Vec<bool>,
    identity_cells: IdentityCells,
    polys: Vec<Polynomial<C::Scalar, Coeff>>,
    pub(super) cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
}

const IDENTITY_BITS_PER_BYTE: usize = u8::BITS as usize;
const SPARSE_ACTIVE_ROW_FRACTION_DENOMINATOR: usize = 3;

#[derive(Clone, Debug)]
struct IdentityCells(Vec<Vec<u8>>);

impl IdentityCells {
    fn encoded_column_len(rows: usize) -> usize {
        rows.div_ceil(IDENTITY_BITS_PER_BYTE)
    }

    fn from_mapping(mapping: &[Vec<(usize, usize)>]) -> Self {
        Self(
            mapping
                .iter()
                .enumerate()
                .map(|(column, mapping)| {
                    let mut identity = vec![0; Self::encoded_column_len(mapping.len())];
                    for (row, &permuted) in mapping.iter().enumerate() {
                        if permuted == (column, row) {
                            identity[row / IDENTITY_BITS_PER_BYTE] |=
                                1_u8 << (row % IDENTITY_BITS_PER_BYTE);
                        }
                    }
                    identity
                })
                .collect(),
        )
    }

    fn identity_columns(&self, rows: usize) -> Vec<bool> {
        let full_bytes = rows / IDENTITY_BITS_PER_BYTE;
        let trailing_bits = rows % IDENTITY_BITS_PER_BYTE;
        assert!(
            self.0
                .iter()
                .all(|column| column.len() == Self::encoded_column_len(rows))
        );

        self.0
            .iter()
            .map(|column| {
                column[..full_bytes].iter().all(|&byte| byte == u8::MAX)
                    && (trailing_bits == 0 || column[full_bytes] == (1_u8 << trailing_bits) - 1)
            })
            .collect()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn chunks(&self, chunk_size: usize) -> std::slice::Chunks<'_, Vec<u8>> {
        self.0.chunks(chunk_size)
    }

    fn contains(column: &[u8], row: usize) -> bool {
        column[row / IDENTITY_BITS_PER_BYTE] & (1_u8 << (row % IDENTITY_BITS_PER_BYTE)) != 0
    }

    fn active_row_count(columns: &[Vec<u8>], rows: usize) -> usize {
        let encoded_rows = Self::encoded_column_len(rows);
        assert!(columns.iter().all(|column| column.len() >= encoded_rows));

        (0..encoded_rows)
            .map(|byte| {
                let all_identity = columns
                    .iter()
                    .fold(u8::MAX, |identity, column| identity & column[byte]);
                let valid_bits =
                    if byte + 1 == encoded_rows && !rows.is_multiple_of(IDENTITY_BITS_PER_BYTE) {
                        (1_u8 << (rows % IDENTITY_BITS_PER_BYTE)) - 1
                    } else {
                        u8::MAX
                    };
                ((!all_identity) & valid_bits).count_ones() as usize
            })
            .sum()
    }

    fn should_use_sparse(columns: &[Vec<u8>], rows: usize) -> bool {
        Self::active_row_count(columns, rows) <= rows / SPARSE_ACTIVE_ROW_FRACTION_DENOMINATOR
    }

    #[cfg(test)]
    fn clear(&mut self) {
        self.0.iter_mut().for_each(|column| column.fill(0));
    }
}

#[cfg(test)]
mod tests {
    use super::{IDENTITY_BITS_PER_BYTE, IdentityCells, SPARSE_ACTIVE_ROW_FRACTION_DENOMINATOR};

    fn mapping_with_identity_rows(
        column: usize,
        rows: usize,
        identity_rows: &[usize],
    ) -> Vec<(usize, usize)> {
        let mut mapping = (0..rows)
            .map(|row| (column, (row + 1) % rows))
            .collect::<Vec<_>>();
        for &row in identity_rows {
            mapping[row] = (column, row);
        }
        mapping
    }

    #[test]
    fn identity_cells_pack_byte_boundaries_and_real_domain_end() {
        const REAL_ROW_COUNT: usize = 1 << 11;
        let identity_rows = [0, 7, 8, REAL_ROW_COUNT - 1];
        let identity = IdentityCells::from_mapping(&[mapping_with_identity_rows(
            0,
            REAL_ROW_COUNT,
            &identity_rows,
        )]);

        assert_eq!(identity.0[0].len(), REAL_ROW_COUNT / IDENTITY_BITS_PER_BYTE);
        for row in identity_rows {
            assert!(IdentityCells::contains(&identity.0[0], row));
        }
        for row in [1, 6, 9, REAL_ROW_COUNT - 2] {
            assert!(!IdentityCells::contains(&identity.0[0], row));
        }
    }

    #[test]
    fn identity_cells_round_non_byte_aligned_lengths_up() {
        const ROW_COUNT: usize = 10;
        let identity = IdentityCells::from_mapping(&[mapping_with_identity_rows(
            0,
            ROW_COUNT,
            &[ROW_COUNT - 1],
        )]);

        assert_eq!(identity.0[0].len(), 2);
        assert!(IdentityCells::contains(&identity.0[0], ROW_COUNT - 1));
        assert!(!IdentityCells::contains(&identity.0[0], ROW_COUNT - 2));
    }

    #[test]
    fn identity_cells_count_active_rows_across_bytes_and_ignore_padding() {
        const ROW_COUNT: usize = 10;
        let all_rows = (0..ROW_COUNT).collect::<Vec<_>>();
        let all_but_boundary_rows = (0..ROW_COUNT)
            .filter(|&row| !matches!(row, 7 | 8))
            .collect::<Vec<_>>();
        let identity = IdentityCells::from_mapping(&[
            mapping_with_identity_rows(0, ROW_COUNT, &all_rows),
            mapping_with_identity_rows(1, ROW_COUNT, &all_but_boundary_rows),
        ]);

        assert_eq!(identity.identity_columns(ROW_COUNT), [true, false]);
        assert_eq!(IdentityCells::active_row_count(&identity.0, ROW_COUNT), 2);
    }

    #[test]
    fn sparse_route_includes_the_active_row_threshold_boundary() {
        const ROW_COUNT: usize = 12;
        const MAX_SPARSE_ACTIVE_ROWS: usize = ROW_COUNT / SPARSE_ACTIVE_ROW_FRACTION_DENOMINATOR;
        let first_identity_rows = (2..ROW_COUNT).collect::<Vec<_>>();
        let second_identity_rows = (0..2).chain(4..ROW_COUNT).collect::<Vec<_>>();
        let at_threshold = IdentityCells::from_mapping(&[
            mapping_with_identity_rows(0, ROW_COUNT, &first_identity_rows),
            mapping_with_identity_rows(1, ROW_COUNT, &second_identity_rows),
        ]);
        assert_eq!(
            IdentityCells::active_row_count(&at_threshold.0, ROW_COUNT),
            MAX_SPARSE_ACTIVE_ROWS,
        );
        assert!(IdentityCells::should_use_sparse(&at_threshold.0, ROW_COUNT));

        let second_identity_rows = (0..2).chain(5..ROW_COUNT).collect::<Vec<_>>();
        let over_threshold = IdentityCells::from_mapping(&[
            mapping_with_identity_rows(0, ROW_COUNT, &first_identity_rows),
            mapping_with_identity_rows(1, ROW_COUNT, &second_identity_rows),
        ]);
        assert_eq!(
            IdentityCells::active_row_count(&over_threshold.0, ROW_COUNT),
            MAX_SPARSE_ACTIVE_ROWS + 1,
        );
        assert!(!IdentityCells::should_use_sparse(
            &over_threshold.0,
            ROW_COUNT
        ));
    }
}
