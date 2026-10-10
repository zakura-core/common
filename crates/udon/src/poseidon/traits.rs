//! Consumer views of the fixed Poseidon parameter sets.

use super::{PALLAS_BASE, PALLAS_BASE_T3, PALLAS_SCALAR, PALLAS_SCALAR_T3};
use crate::field::{Field, FieldAdapter, PallasBase, PallasScalar, PastaField, PrimeModulus};

pub(super) fn parameter_rows<M: PrimeModulus, const N: usize>(
    rows: &[[PastaField<M>; N]],
) -> &[[FieldAdapter<M>; N]] {
    // Flattening fixed-width rows gives a multiple of N elements, so the
    // borrowed view can be split back into the same rows without a remainder.
    FieldAdapter::from_slice(rows.as_flattened())
        .as_chunks::<N>()
        .0
}

/// A Poseidon permutation over `F`, described to code generic over the
/// instance.
///
/// The shape constants size states and sponges at compile time; the tables
/// are borrowed from the instance. [`PoseidonFp`] and [`PoseidonFq`] expose the
/// width-five instances; [`PoseidonFpT3`] and [`PoseidonFqT3`] expose width three.
pub trait PoseidonPermutation<F: Field>: Send + Sync + 'static {
    /// The representation shared by round-constant and MDS rows.
    ///
    /// Each row must expose exactly [`T`](Self::T) field elements. Pasta uses
    /// the same fixed-size arrays as its native [`super::PoseidonParameters`].
    type Row: AsRef<[F]>;

    /// The state width.
    const T: usize;

    /// The sponge rate: how many elements are absorbed or squeezed between
    /// permutations. Smaller than [`T`](Self::T).
    const RATE: usize;

    /// The number of full rounds, half before and half after the partial
    /// rounds.
    const FULL_ROUNDS: usize;

    /// The number of partial rounds, which apply the S-box to the first state
    /// element only.
    const PARTIAL_ROUNDS: usize;

    /// The positive S-box exponent: the map `x -> x^ALPHA`, a permutation of `F`.
    const ALPHA: u32;

    /// Borrows the round constants in application order.
    ///
    /// Contains [`FULL_ROUNDS`](Self::FULL_ROUNDS) plus
    /// [`PARTIAL_ROUNDS`](Self::PARTIAL_ROUNDS) rows of [`T`](Self::T) elements.
    fn round_constants(&self) -> &[Self::Row];

    /// Borrows the [`T`](Self::T) rows of the square MDS matrix.
    fn mds_matrix(&self) -> &[Self::Row];
}

/// The [`PALLAS_BASE`] instance as a [`PoseidonPermutation`] over [`FieldAdapter<PallasBase>`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PoseidonFp;

/// The [`PALLAS_SCALAR`] instance as a [`PoseidonPermutation`] over [`FieldAdapter<PallasScalar>`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PoseidonFq;

/// The width-three [`PALLAS_BASE_T3`] instance as a [`PoseidonPermutation`]
/// over [`FieldAdapter<PallasBase>`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PoseidonFpT3;

/// The width-three [`PALLAS_SCALAR_T3`] instance as a [`PoseidonPermutation`]
/// over [`FieldAdapter<PallasScalar>`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PoseidonFqT3;

macro_rules! poseidon_permutation {
    ($name:ident, $field:ty, $parameters:expr) => {
        impl PoseidonPermutation<$field> for $name {
            type Row = [$field; $parameters.width()];

            const T: usize = $parameters.width();
            const RATE: usize = $parameters.rate();
            const FULL_ROUNDS: usize = $parameters.full_rounds;
            const PARTIAL_ROUNDS: usize = $parameters.partial_rounds;
            const ALPHA: u32 = $parameters.alpha;

            fn round_constants(&self) -> &[Self::Row] {
                parameter_rows($parameters.round_constants)
            }

            fn mds_matrix(&self) -> &[Self::Row] {
                parameter_rows($parameters.mds)
            }
        }
    };
}

poseidon_permutation!(PoseidonFp, FieldAdapter<PallasBase>, PALLAS_BASE);
poseidon_permutation!(PoseidonFq, FieldAdapter<PallasScalar>, PALLAS_SCALAR);
poseidon_permutation!(PoseidonFpT3, FieldAdapter<PallasBase>, PALLAS_BASE_T3);
poseidon_permutation!(PoseidonFqT3, FieldAdapter<PallasScalar>, PALLAS_SCALAR_T3);
