//! The embedded fixed proving target.
//!
//! The embedded `.pod` artifacts are generated into `OUT_DIR` on every build
//! from the canonical raw inputs under `data/raw/` (by `sensei-artifacts`, through
//! the shared `sensei-shared` description) and store their contents in the
//! exact in-memory representation (Montgomery limbs, affine point records).
//! They are mapped straight into typed `&'static` views through
//! [`crate::static_data`] — no parsing, conversion, or point arithmetic
//! touches them at load. Their digests and semantic invariants are pinned by
//! this module's tests rather than checked at runtime. [`FixedTarget`] builds
//! the remaining derived state: dense fixed
//! and sigma columns expanded from the sparse embedded forms, extended-coset
//! polynomial transforms, prepared gate selectors, structured commitment
//! bases, and the domain, boundary, and permutation-identity
//! vectors. It also provides the blinded commitment entry points over the
//! embedded generators.
//!
//! [`FixedTarget::build`] composes the prepared target here. [`embedded`]
//! declares its static artifact views; [`prepared`] owns the row/polynomial
//! containers; [`domain`] implements domain, boundary, and instance preparation.
//! Shared records remain here with private fields for composition and tests.
//! [`commitments`] implements the commitment operations and prepares their
//! structured bases. [`copy_constraints`] derives both the preflight equality
//! classes and the active edges used by permutation products from the same sigma
//! map. The adjacent test module pins artifact bytes and independently checks
//! derived and embedded representations.

use alloc::{boxed::Box, sync::Arc, vec::Vec};
mod commitments;
mod copy_constraints;
mod domain;
mod embedded;
mod prepared;

#[cfg(test)]
use crate::native::polynomial::base_lagrange_to_extended_coset;
use crate::native::queries::{
    ADVICE_QUERIES, FIXED_QUERIES, INSTANCE_QUERIES, PERMUTATION_COLUMNS,
};

use super::commitment::{FixedGenerator, FoldingGenerators};
use super::curve::{PallasAffine, PreparedAffinePoint, Vesta};
use super::field::Fp;
use super::generated_expressions::{
    ExpressionRange, GATE_CONSTRAINT_COUNT, GATES, LOOKUPS, LookupExpressionRanges,
    PREPARED_GATE_SELECTOR_FIXED_QUERY, PREPARED_GATE_SELECTOR_ROW,
};
#[cfg(not(embed_gate_selectors))]
use super::generated_expressions::{
    GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, QueryKind, prepare_gate_selectors,
};
use super::polynomial::FpCosetTiles;
use super::srs::PreparedSrs;
use commitments::WindowSelection;
use copy_constraints::{derive_copy_classes, derive_permutation_edge_schedule};
use embedded::*;
#[cfg(not(all(embed_fixed_coefficients, embed_sigma_coefficients)))]
use prepared::derive_coefficient_columns;

#[cfg(embed_window_tables)]
pub(crate) use embedded::WINDOW_TABLES;
pub(crate) use prepared::{
    CoefficientColumns, GateSelectorRows, PreparedPolynomials, PreparedRows,
};

pub(crate) use crate::native::queries::{ColumnKind, PermutationColumn, Query};
pub(crate) use commitments::{
    BitColumnBases, ConstantColumn, LagrangeCommitScalars, LookupCommitPair, WordColumnBases,
};
pub(crate) use copy_constraints::{ChunkEdgeSchedule, CopyClasses};
pub(crate) use sensei_shared::{
    ADVICE_COLUMNS, BLINDING_FACTORS, EXTENDED_N, FIXED_COLUMNS, INSTANCE_VALUE_COUNT, K, N,
    PERMUTATION_CHUNK_LEN, PERMUTATION_COLUMN_COUNT, PERMUTATION_SETS, QUOTIENT_PIECES,
    USABLE_ROWS_END,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TargetError {
    Malformed,
    Dimension,
}

pub(crate) struct Parameters {
    srs: Arc<PreparedSrs>,
    residual_copies: commitments::ResidualCopies,
    folding_generators: FoldingGenerators,
    sparse_mask_generators: Vec<FixedGenerator>,
    sorted_lookup_suffixes: commitments::SuffixGenerators,
    /// Prefix sums `P[j] = Σ_{i<j} G_i` of the Lagrange SRS for `j` in
    /// `1..=USABLE_ROWS_END`, stored at index `j - 1` and prepared as MSM
    /// bases, followed by the plain blinding-tail generators
    /// `G_{USABLE_ROWS_END}..G_{N-1}` so one index-selected MSM job covers a
    /// telescoped piecewise-constant prefix plus its dense tail. An identity
    /// prefix would have no affine MSM representation; the pinned SRS has
    /// none, which the embedded-data tests confirm.
    lagrange_prefix_sums: Vec<PreparedAffinePoint<Vesta>>,
    /// `H = Σ_r G_r` over the variable-base gadget's repeated-coordinate rows
    /// ([`crate::native::regions::variable_base_mul::coordinate_rows`]), prepared as a fixed base
    /// with window tables. Each of the two coordinate columns holds one run
    /// of equal cells `v` on exactly those rows, so its commitment folds the
    /// run into the single term `v·H`. Derived during preparation from
    /// the embedded prefix sums (`P[end] − P[start]`); SRS and layout only.
    repeated_coordinate_base: FixedGenerator,
    /// Per running-sum column, the weighted generators that transpose the
    /// Sinsemilla hashes' running sums onto their ten-bit words: for a
    /// piece at rows `r_0..r_{m-1}`, `H_0 = G_{r_0}`, `H_j = G_{r_j} + B·H_{j-1}`,
    /// and the remainder base `B·H_{m-1}`, so that
    /// `Σ z_i G_{r_i} = Σ_j d_j H_j + t·B·H_{m-1}` for the words
    /// `d_j = z_j − B·z_{j+1}` and remainder `t = z_m` — an identity for any
    /// cell values, fast when the words are small. Derived during preparation
    /// from the embedded Lagrange bases and the shared hash schedule.
    word_bases: Vec<WordColumnBases>,
    /// Per column of the variable-base gadget's binary running-sum chains,
    /// the bases that transpose each chain onto one general term for its
    /// initial sum plus one term per bit: `Σ_i z_i G_{r_i} = z_0·K +
    /// Σ_{k≥1} b_k H_k` with `b_k = z_k − 2·z_{k−1}`, `H_k = Σ_{i≥k} 2^{i−k}
    /// G_{r_i}`, `K = Σ_i 2^i G_{r_i}` — an identity for any cell values,
    /// cheap when the bits are 0/1 (one bucket deposit each). Derived once
    /// during preparation from the Lagrange bases and the shared chain footprint.
    bit_bases: Vec<BitColumnBases>,
    /// Per column that already carries a batch-lifetime copy, the writer's
    /// nonzero constant cells and their precomputed offset `Σ k·G_row`:
    /// the cells are zeroed in the copy and the offset added once. A
    /// cell that does not hold its constant stays dense with an exact
    /// correction term, so the commitment is right for any values.
    constant_columns: Vec<ConstantColumn>,
    /// The fixed-base windows whose selected coordinate cells the `X_COLUMN`
    /// and `Y_COLUMN` commitments replace by one precomputed point each from
    /// [`FIXED_WINDOW_X_BASES`] / [`FIXED_WINDOW_Y_BASES`]: per window,
    /// its row and the eight coordinate values the writer selects among, so
    /// the digit is recovered by exact comparison against the same table
    /// entry the writer wrote. One selection per coordinate column.
    window_selections: Vec<WindowSelection>,
    advice_carveouts: [Vec<commitments::Carveout>; ADVICE_COLUMNS],
    /// `G_0`, the first coefficient generator, prepared with window tables:
    /// the IPA mask's constant term `−Σ α_i x_3^{2^i}` is the one mask
    /// coefficient that waits for `x_3`, so it is applied as one prepared
    /// fixed-base multiplication after the rest of the mask commitment has
    /// been formed in the quotient stage's piece batch. See
    /// [`super::prover::IpaMaskEarly`] for the complete split commitment.
    prepared_first_coefficient_generator: FixedGenerator,
}

pub(crate) struct FixedTarget {
    fft: super::polynomial::PreparedFft,
    lookup_preparation: super::prover::LookupPreparation,
    window_tables: PreparedRows<[sensei_shared::WindowTableEntry; 8]>,
    parameters: Parameters,
    vk_representative: Fp,
    fixed_values: Vec<[Fp; N]>,
    sigma_values: Vec<[Fp; N]>,
    fixed_polynomials: PreparedPolynomials,
    gate_selectors: Option<GateSelectorRows>,
    gate_active_rows: GateActiveRows,
    preflight: super::preflight::PreparedPreflight,
    sigma_polynomials: PreparedPolynomials,
    /// Raw copy-graph data, retained for the census tests; production code
    /// consumes it only through the derived edge schedule and copy classes.
    #[cfg(test)]
    sigma_mapping: &'static [[u16; N]],
    permutation_edge_schedule: Vec<ChunkEdgeSchedule>,
    copy_classes: CopyClasses,
    queries: Queries,
    permutation_columns: &'static [PermutationColumn],
    permutation_identities: PermutationIdentities,
    prepared_instance: PreparedInstance,
    domain: Domain,
    boundaries: Boundaries,
}

pub(crate) struct Queries {
    advice: &'static [Query],
    fixed: &'static [Query],
    instance: &'static [Query],
}

pub(crate) struct Domain {
    omega: Fp,
    omega_inverse: Fp,
    extended_omega: Fp,
    coset_generator: Fp,
    permutation_delta: Fp,
    vanishing_inverses: [Fp; EXTENDED_N / N],
}

/// The extended-coset boundary polynomials, embedded or transformed at load —
/// equal field values either way (the `embed_boundaries` dial). The
/// embedded variant exists only when its dial is on, so the default
/// configuration compiles to a single-variant enum: the layout of the plain
/// derived record, with no discriminant and irrefutable matches.
pub(crate) enum Boundaries {
    #[cfg(embed_boundaries)]
    Embedded(&'static [[Fp; EXTENDED_N]; 3]),
    #[cfg_attr(all(embed_boundaries, not(test)), allow(dead_code))]
    Derived {
        l_0: Vec<Fp>,
        l_last: Vec<Fp>,
        active_rows: Vec<Fp>,
    },
}

/// Prepared active-row lists for the gate programs with a fixed-only root
/// factor: the base-domain rows where the factor is non-zero. The factors are
/// pure functions of the embedded fixed columns, so preflight can check each
/// constraint's dynamic body at these rows alone. Constraints whose factors
/// are byte-identical (a gate's constraints share its selector product) share
/// one list.
pub(crate) struct GateActiveRows {
    /// One ascending row list per distinct factor byte-content.
    lists: Vec<Vec<u16>>,
    /// Gate expression -> index into `lists`; every gate is populated at load.
    per_expression: [Option<u16>; GATE_CONSTRAINT_COUNT],
}

// Rows and list indices are stored as `u16`.
const _: () = assert!(N <= 1usize << 16 && GATE_CONSTRAINT_COUNT <= u16::MAX as usize);

/// Derives the nonzero-row lists of every distinct gate fixed root factor
/// over the base-domain fixed values, deduplicated by structural equality.
/// Per-factor jobs are independent, so the result is bit-identical for any
/// worker count.
fn derive_gate_active_rows(fixed_values: &[[Fp; N]]) -> Result<GateActiveRows, TargetError> {
    let mut unique = Vec::with_capacity(GATE_CONSTRAINT_COUNT);
    let mut per_expression = [None; GATE_CONSTRAINT_COUNT];
    for (expression, slot) in per_expression.iter_mut().enumerate() {
        let factor = super::compiled_expressions::program(expression)
            .map_err(|_| TargetError::Malformed)?
            .fixed_factor()
            .ok_or(TargetError::Malformed)?;
        let index = unique
            .iter()
            .position(|&existing| existing == factor)
            .unwrap_or_else(|| {
                unique.push(factor);
                unique.len() - 1
            });
        *slot = Some(index as u16);
    }
    let lists = (unique)
        .into_iter()
        .map(|factor| -> Result<_, crate::Error> {
            let mut evaluation = factor.bind_fixed(fixed_values)?;
            Ok((0..N)
                .filter(|&row| !evaluation.evaluate(row).is_zero())
                .map(|row| row as u16)
                .collect::<Vec<_>>())
        })
        .collect::<Vec<_>>()
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| TargetError::Malformed)?;
    Ok(GateActiveRows {
        lists,
        per_expression,
    })
}

pub(crate) struct PermutationIdentities {
    values: Vec<[Fp; N]>,
    deltas: Vec<Fp>,
}

/// Residue-major cosets: tile s contains rows s + 8k in each column.
/// Embedded columns are already in this layout and are borrowed directly.
pub(crate) enum CosetColumns {
    Derived(Vec<super::buffer::Buffer<Fp>>),
    #[cfg(any(embed_fixed_cosets, embed_sigma_cosets))]
    Embedded(&'static [[Fp; EXTENDED_N]]),
}

/// The prepared instance polynomial machinery over the populated prefix.
///
/// `coefficients` are the transposed coefficient bases for the populated
/// instance rows, embedded or derived at load — equal field values either
/// way (the `embed_instance_bases` dial). Openings combine the prefixes across
/// Actions before applying these bases inside their coefficient sum. The
/// extended coset instead factors each instance polynomial
/// through the fixed support: with `H(X) = ∏_{j<m} (X − ω^j)` over the `m`
/// populated rows, `S(X) = (X^N − 1) / H(X)` vanishes on every unpopulated
/// row, so the instance polynomial is exactly `S · q` for the degree-below-`m`
/// `q` interpolating `q(ω^j) = instance[j] / S(ω^j)`. `support` holds `S` on
/// the extended coset and `interpolation[k]` the `m` coefficients producing
/// `q`'s coefficient `k`; both are derived once at load from the domain
/// alone and are shared by every proof.
pub(crate) struct PreparedInstance {
    coefficients: InstanceBasisRows,
    support: Arc<FpCosetTiles>,
    interpolation: Box<[[Fp; INSTANCE_VALUE_COUNT]; INSTANCE_VALUE_COUNT]>,
}

/// Transposed instance coefficient bases, `N` rows of the populated prefix's
/// width, embedded or derived at load (the `embed_instance_bases` dial).
type InstanceBasisRows = PreparedRows<[Fp; INSTANCE_VALUE_COUNT]>;

impl FixedTarget {
    /// Builds the derived prepared state over the embedded static data.
    /// Coset expansion uses the caller's executor and task budget. Other
    /// derivations are serial and independent of execution order.
    pub(crate) fn build(
        srs: Arc<PreparedSrs>,
        execution: super::worker::Execution<'_>,
    ) -> Result<Self, TargetError> {
        let fft = super::polynomial::PreparedFft::new();
        let vk_representative = super::protocol::vk_representative();
        let fixed_values = sensei_shared::fixed_columns::build_fixed_values(
            crate::primitives::tables::sinsemilla_generators(),
            FIXED_TUPLES,
            TUPLE_ASSIGNMENTS,
        );
        let lookup_preparation = super::prover::LookupPreparation::new(&fixed_values)
            .map_err(|_| TargetError::Malformed)?;
        #[cfg(embed_window_tables)]
        let window_tables = PreparedRows::embedded(
            WINDOW_TABLES,
            sensei_shared::fixed_bases::FIXED_BASE_TOTAL_WINDOWS,
        )?;
        #[cfg(not(embed_window_tables))]
        let window_tables = PreparedRows::derived(
            sensei_shared::fixed_bases::build_fixed_base_window_tables()
                .ok_or(TargetError::Malformed)?,
            sensei_shared::fixed_bases::FIXED_BASE_TOTAL_WINDOWS,
        )?;
        let domain = Domain::derive()?;
        let (sigma_values, identity_values) = sensei_shared::permutation::sigma_lagrange_values(
            SIGMA_MAP,
            domain.omega(),
            domain.permutation_delta(),
        );
        #[cfg(embed_fixed_coefficients)]
        let fixed_coefficients =
            CoefficientColumns::embedded(FIXED_COEFFICIENTS, fixed_values.len())?;
        #[cfg(not(embed_fixed_coefficients))]
        let fixed_coefficients = CoefficientColumns::derived(
            derive_coefficient_columns(&fixed_values, &fft)?,
            fixed_values.len(),
        )?;
        #[cfg(embed_fixed_cosets)]
        let fixed_embedded_cosets = Some(&FIXED_COSETS[..]);
        #[cfg(not(embed_fixed_cosets))]
        let fixed_embedded_cosets = None;
        let fixed_polynomials = PreparedPolynomials::prepare(
            fixed_coefficients,
            fixed_embedded_cosets,
            &fft,
            execution,
        )?;
        #[cfg(embed_gate_selectors)]
        let gate_selectors = Some(GateSelectorRows::embedded(GATE_SELECTORS, EXTENDED_N)?);
        #[cfg(not(embed_gate_selectors))]
        let gate_selectors = if crate::tuning::GATE_SELECTORS
            == crate::tuning::OptionalPreparation::OnDemand
        {
            None
        } else {
            // Collect directly into the final matrix: no second full-size chunk store.
            Some(GateSelectorRows::derived(
                (0..EXTENDED_N)
                    .map(|row| {
                        let queries: [Fp; GATE_QUERY_COUNT] = core::array::from_fn(|frame_index| {
                            match GATE_QUERY_DESCRIPTORS[frame_index] {
                                (QueryKind::Fixed, query_index) => {
                                    let query = FIXED_QUERIES[query_index];
                                    fixed_polynomials.cosets().column(query.column)[row]
                                }
                                (QueryKind::Advice | QueryKind::Instance, _) => <Fp>::ZERO,
                            }
                        });
                        prepare_gate_selectors(&queries)
                    })
                    .collect(),
                EXTENDED_N,
            )?)
        };
        let selector_query = FIXED_QUERIES[PREPARED_GATE_SELECTOR_FIXED_QUERY];
        if selector_query.rotation != 0 {
            return Err(TargetError::Dimension);
        }
        let gate_active_rows = derive_gate_active_rows(&fixed_values)?;
        #[cfg(embed_sigma_coefficients)]
        let sigma_coefficients =
            CoefficientColumns::embedded(SIGMA_COEFFICIENTS, sigma_values.len())?;
        #[cfg(not(embed_sigma_coefficients))]
        let sigma_coefficients = CoefficientColumns::derived(
            derive_coefficient_columns(&sigma_values, &fft)?,
            sigma_values.len(),
        )?;
        #[cfg(embed_sigma_cosets)]
        let sigma_embedded_cosets = Some(&SIGMA_COSETS[..]);
        #[cfg(not(embed_sigma_cosets))]
        let sigma_embedded_cosets = None;
        let sigma_polynomials = PreparedPolynomials::prepare(
            sigma_coefficients,
            sigma_embedded_cosets,
            &fft,
            execution,
        )?;
        let queries = Queries {
            advice: &ADVICE_QUERIES,
            fixed: &FIXED_QUERIES,
            instance: &INSTANCE_QUERIES,
        };
        let permutation_columns = &PERMUTATION_COLUMNS;
        if permutation_columns.len() != sigma_values.len() {
            return Err(TargetError::Dimension);
        }
        let permutation_identities = PermutationIdentities::derive(identity_values)?;
        let permutation_edge_schedule = derive_permutation_edge_schedule(SIGMA_MAP)?;
        let copy_classes = derive_copy_classes(SIGMA_MAP)?;
        #[cfg(embed_instance_bases)]
        let prepared_instance =
            PreparedInstance::new(InstanceBasisRows::embedded(INSTANCE_BASES, N)?)?;
        #[cfg(not(embed_instance_bases))]
        let prepared_instance = PreparedInstance::derive()?;
        #[cfg(embed_boundaries)]
        let boundaries = Boundaries::Embedded(BOUNDARY_POLYNOMIALS);
        #[cfg(not(embed_boundaries))]
        let boundaries = Boundaries::derive()?;
        let mut target = Self {
            parameters: Parameters::over_srs(srs, window_tables.rows(), &copy_classes)?,
            lookup_preparation,
            fft,
            window_tables,
            vk_representative,
            fixed_values,
            sigma_values,
            fixed_polynomials,
            gate_selectors,
            gate_active_rows,
            preflight: super::preflight::PreparedPreflight::default(),
            sigma_polynomials,
            #[cfg(test)]
            sigma_mapping: SIGMA_MAP,
            permutation_edge_schedule,
            copy_classes,
            queries,
            permutation_columns,
            permutation_identities,
            prepared_instance,
            domain,
            boundaries,
        };
        target.preflight = super::preflight::PreparedPreflight::new(&target)
            .map_err(|_| TargetError::Malformed)?;
        Ok(target)
    }

    pub(crate) fn preflight(&self) -> &super::preflight::PreparedPreflight {
        &self.preflight
    }

    pub(crate) fn fft(&self) -> &super::polynomial::PreparedFft {
        &self.fft
    }
    pub(crate) fn lookup_preparation(&self) -> &super::prover::LookupPreparation {
        &self.lookup_preparation
    }
    pub(crate) fn window_tables(&self) -> &[[sensei_shared::WindowTableEntry; 8]] {
        self.window_tables.rows()
    }
    pub(crate) fn parameters(&self) -> &Parameters {
        &self.parameters
    }

    pub(crate) fn vk_representative(&self) -> &Fp {
        &self.vk_representative
    }

    pub(crate) fn fixed_values(&self) -> &[[Fp; N]] {
        &self.fixed_values
    }

    pub(crate) fn sinsemilla_generators(&self) -> &'static [PallasAffine] {
        crate::primitives::tables::sinsemilla_generators()
    }

    pub(crate) fn sigma_values(&self) -> &[[Fp; N]] {
        &self.sigma_values
    }

    pub(crate) fn fixed_polynomials(&self) -> &PreparedPolynomials {
        &self.fixed_polynomials
    }

    /// Complete fixed-only selectors for each extended row, including all
    /// seven-root tails (see `PREPARED_GATE_SELECTOR_ROW`).
    pub(crate) fn gate_selectors(&self) -> Option<&[[Fp; PREPARED_GATE_SELECTOR_ROW]]> {
        self.gate_selectors.as_ref().map(PreparedRows::rows)
    }

    /// The precomputed active rows of a gate expression's fixed root factor,
    /// or `None` when the index is outside the prepared gate programs.
    pub(crate) fn gate_active_rows(&self, expression: usize) -> Option<&[u16]> {
        let index = (*self.gate_active_rows.per_expression.get(expression)?)?;
        Some(&self.gate_active_rows.lists[usize::from(index)])
    }

    pub(crate) fn sigma_polynomials(&self) -> &PreparedPolynomials {
        &self.sigma_polynomials
    }

    #[cfg(test)]
    pub(crate) fn sigma_mapping(&self) -> &[[u16; N]] {
        self.sigma_mapping
    }

    pub(crate) fn permutation_edge_schedule(&self) -> &[ChunkEdgeSchedule] {
        &self.permutation_edge_schedule
    }

    pub(crate) fn copy_classes(&self) -> &CopyClasses {
        &self.copy_classes
    }

    pub(crate) fn queries(&self) -> &Queries {
        &self.queries
    }

    pub(crate) fn permutation_columns(&self) -> &[PermutationColumn] {
        self.permutation_columns
    }

    pub(crate) fn permutation_identities(&self) -> &PermutationIdentities {
        &self.permutation_identities
    }

    pub(crate) fn prepared_instance(&self) -> &PreparedInstance {
        &self.prepared_instance
    }

    pub(crate) fn gates(&self) -> &'static [ExpressionRange] {
        GATES
    }

    pub(crate) fn lookups(&self) -> &'static [LookupExpressionRanges] {
        LOOKUPS
    }

    pub(crate) fn domain(&self) -> &Domain {
        &self.domain
    }

    pub(crate) fn boundaries(&self) -> &Boundaries {
        &self.boundaries
    }
}

impl Queries {
    pub(crate) fn advice(&self) -> &[Query] {
        self.advice
    }

    pub(crate) fn fixed(&self) -> &[Query] {
        self.fixed
    }

    pub(crate) fn instance(&self) -> &[Query] {
        self.instance
    }
}

#[cfg(test)]
fn boundary_polynomial(rows: impl IntoIterator<Item = usize>) -> Result<Vec<Fp>, TargetError> {
    let mut values = alloc::vec![ <Fp>::ZERO; N];
    for row in rows {
        let value = values.get_mut(row).ok_or(TargetError::Dimension)?;
        if !value.is_zero() {
            return Err(TargetError::Dimension);
        }
        *value = <Fp>::ONE;
    }
    if !base_lagrange_to_extended_coset(&mut values) {
        return Err(TargetError::Dimension);
    }
    Ok(values)
}

#[cfg(test)]
mod tests;
