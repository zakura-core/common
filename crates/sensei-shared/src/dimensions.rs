//! Circuit dimensions and the protocol relationships between them.
//!
//! Row counts, column counts, and degree bounds describe the fixed Ironwood
//! circuit. They are not prover tuning parameters. The assertions below pin
//! derived dimensions and the relationships used by allocation and loop bounds.

/// Log2 of the circuit's row count.
pub const K: u32 = 11;
/// The circuit's row count (and SRS vector length), `2^K`.
pub const N: usize = 1 << K;
/// The largest total degree of any constraint the circuit enforces: Halo 2's
/// degree bound, from which the quotient, extended-domain, and permutation
/// chunk sizes all follow.
pub const CONSTRAINT_DEGREE: usize = 9;
/// Pieces of `N` coefficients the quotient polynomial splits into: its degree
/// is at most `(CONSTRAINT_DEGREE - 1) · N`.
pub const QUOTIENT_PIECES: usize = CONSTRAINT_DEGREE - 1;
/// Log2 of the extended evaluation domain's row count: the smallest power of
/// two holding `QUOTIENT_PIECES` copies of the base domain.
pub const EXTENDED_K: u32 = K + QUOTIENT_PIECES.next_power_of_two().trailing_zeros();
/// The extended evaluation domain's row count (`8N`).
pub const EXTENDED_N: usize = 1 << EXTENDED_K;
/// Number of trailing rows reserved for random masks in blinded columns.
pub const BLINDING_FACTORS: usize = 5;
/// Exclusive end of usable rows, `N - (BLINDING_FACTORS + 1)`.
///
/// Row `USABLE_ROWS_END` is the `l_last` boundary row. The random-mask rows
/// follow it at `USABLE_ROWS_END + 1..N`. The prepared Lagrange prefix-sum
/// table covers sums `P[j]` for `j` in `1..=USABLE_ROWS_END`.
pub const USABLE_ROWS_END: usize = N - (BLINDING_FACTORS + 1);
/// Fixed columns of the circuit.
pub const FIXED_COLUMNS: usize = 29;
/// Advice (witness) columns of the circuit.
pub const ADVICE_COLUMNS: usize = 10;
/// Instance (public input) columns of the circuit.
pub const INSTANCE_COLUMNS: usize = 1;
/// Columns participating in the permutation argument.
pub const PERMUTATION_COLUMN_COUNT: usize = 15;
/// Columns per permutation grand-product set, `CONSTRAINT_DEGREE - 2`: each
/// set's product constraint multiplies that many `(value + β·id + γ)` factors
/// under the `l_0`/`l_last`-style selector within the degree bound.
pub const PERMUTATION_CHUNK_LEN: usize = CONSTRAINT_DEGREE - 2;
/// Permutation grand-product sets: the columns split into chunks of
/// [`PERMUTATION_CHUNK_LEN`], the last one partial.
pub const PERMUTATION_SETS: usize = PERMUTATION_COLUMN_COUNT.div_ceil(PERMUTATION_CHUNK_LEN);
/// Populated rows of the instance column: the prefix carrying public values;
/// every later row is zero.
pub const INSTANCE_VALUE_COUNT: usize = 10;
/// Depth of the note-commitment tree: siblings in one authentication path,
/// hence Merkle layers in one Action's witness.
pub const MERKLE_DEPTH: usize = 32;

const _: () = {
    // Derived values pinned to the protocol's numbers.
    assert!(N == 2_048);
    assert!(QUOTIENT_PIECES == 8);
    assert!(EXTENDED_K == 14 && EXTENDED_N == 16_384);
    assert!(USABLE_ROWS_END == 2_042);
    assert!(PERMUTATION_CHUNK_LEN == 7 && PERMUTATION_SETS == 3);
    // Relationships the prover's allocation sizes and loop bounds rely on.
    assert!(EXTENDED_N == QUOTIENT_PIECES * N);
    assert!(EXTENDED_N.is_multiple_of(N) && (EXTENDED_N / N).is_power_of_two());
    assert!(N - USABLE_ROWS_END == BLINDING_FACTORS + 1);
    assert!(INSTANCE_VALUE_COUNT <= USABLE_ROWS_END);
    assert!(PERMUTATION_SETS * PERMUTATION_CHUNK_LEN >= PERMUTATION_COLUMN_COUNT);
    assert!((PERMUTATION_SETS - 1) * PERMUTATION_CHUNK_LEN < PERMUTATION_COLUMN_COUNT);
    assert!(MERKLE_DEPTH.is_multiple_of(2));
};
