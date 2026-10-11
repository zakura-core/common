//! Sanity checks and value pins for the Pasta Poseidon parameters.

use std::{println, vec::Vec};

use crate::{
    field::{PallasBase, PallasScalar, PastaField, PrimeModulus},
    poseidon::{PALLAS_BASE, PALLAS_SCALAR, PoseidonParameters},
};

#[test]
fn transparent_views_preserve_poseidon_rows() {
    fn check<M: PrimeModulus>() {
        let row = [
            PastaField::ZERO,
            PastaField::from_u64(7),
            PastaField::from_montgomery_limbs(M::MODULUS),
            PastaField::ONE,
            PastaField::from_u64(11),
        ];
        let rows = [row, row.map(|value| value.double())];
        for native in [&rows[..0], &rows[..1], &rows[..]] {
            let borrowed = super::traits::parameter_rows(native);
            assert_eq!(borrowed.len(), native.len());
            assert_eq!(
                borrowed.as_ptr().cast::<[PastaField<M>; 5]>(),
                native.as_ptr()
            );
            assert_eq!(
                bento::bytes_of_slice(borrowed),
                bento::bytes_of_slice(native)
            );
        }
    }
    check::<PallasBase>();
    check::<PallasScalar>();
}

/// FNV-1a over 128 bits, folding every byte into the running hash.
fn fnv1a_128(bytes: impl Iterator<Item = u8>) -> u128 {
    const OFFSET_BASIS: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
    const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;
    bytes.fold(OFFSET_BASIS, |hash, byte| {
        (hash ^ u128::from(byte)).wrapping_mul(PRIME)
    })
}

/// Digest of every table entry as canonical little-endian bytes: the round
/// constants row by row, then the MDS rows. Independent of the Montgomery
/// representation the tables are stored in.
fn digest<M: PrimeModulus, const T: usize>(
    parameters: &PoseidonParameters<PastaField<M>, T>,
) -> u128 {
    fnv1a_128(
        parameters
            .round_constants
            .iter()
            .flatten()
            .chain(parameters.mds.iter().flatten())
            .flat_map(|value| value.to_bytes()),
    )
}

fn assert_well_formed<M: PrimeModulus, const T: usize>(
    parameters: &PoseidonParameters<PastaField<M>, T>,
) {
    assert_eq!(parameters.width(), 5);
    assert_eq!(parameters.rate(), 4);
    assert_eq!(parameters.full_rounds, 8);
    assert_eq!(parameters.partial_rounds, 56);
    assert_eq!(parameters.alpha, 5);
    assert_eq!(parameters.rounds(), 64);
    assert_eq!(parameters.round_constants.len(), 64);

    let all = || {
        parameters
            .round_constants
            .iter()
            .flatten()
            .chain(parameters.mds.iter().flatten())
    };
    assert!(all().all(|value| !value.is_zero()));
    // A transcription slip would most likely repeat or zero an entry.
    let mut seen: Vec<[u8; 32]> = all().map(|value| value.to_bytes()).collect();
    let count = seen.len();
    seen.sort_unstable();
    seen.dedup();
    assert_eq!(seen.len(), count);
}

#[test]
fn pallas_base_parameters_are_well_formed() {
    assert_well_formed(&PALLAS_BASE);
}

#[test]
fn pallas_scalar_parameters_are_well_formed() {
    assert_well_formed(&PALLAS_SCALAR);
}

// The digests pin every one of the 345 entries per field. They were computed
// from tables that matched, entry for entry, the Sage reference captures in
// ragu's `qa/params/reference` at revision 4df34e723c4ee3a1541921aa24821ff86daf4c76
// (`pallas-t5.txt` SHA-256 703f71fd3138e969a74090594fb264c31982623949ec7236c64e92d588942ee1,
// `vesta-t5.txt` SHA-256 b9db55c59b712efa0891cbdb385f6a61566bb1710e66a752e28e761e430e1bbb),
// produced by `daira/pasta-hadeshash` revision 5959f2684a25b372fba347e62467efb00e7e2c3f
// with `generate_parameters_grain.sage 1 0 255 5 8 56 <modulus>`. A table change
// requires re-verifying against that generator before updating a digest; never
// update a digest to make a failing comparison pass.

#[test]
fn pallas_base_tables_match_the_pinned_digest() {
    assert_eq!(digest(&PALLAS_BASE), PALLAS_BASE_DIGEST);
}

#[test]
fn pallas_scalar_tables_match_the_pinned_digest() {
    assert_eq!(digest(&PALLAS_SCALAR), PALLAS_SCALAR_DIGEST);
}

#[test]
fn orchard_parameters_and_hashes_match_legacy_export() {
    fn check<M: PrimeModulus>(parameters: &PoseidonParameters<PastaField<M>, 3>, bytes: &[u8]) {
        assert_eq!(
            (parameters.width(), parameters.rate(), parameters.rounds()),
            (3, 2, 64)
        );
        let (tables, hashes) = bytes.split_at(201 * 32);
        let actual: Vec<_> = parameters
            .round_constants
            .iter()
            .flatten()
            .chain(parameters.mds.iter().flatten())
            .flat_map(|f| f.to_bytes())
            .collect();
        assert_eq!(actual, tables);
        for case in hashes.chunks_exact(96) {
            let decode =
                |bytes: &[u8]| PastaField::<M>::from_bytes(bytes.try_into().unwrap()).unwrap();
            let mut state = [
                decode(&case[..32]),
                decode(&case[32..64]),
                PastaField::<M>::from_u64(2).pow_u64(65),
            ];
            for (round, constants) in parameters.round_constants.iter().enumerate() {
                for (value, constant) in state.iter_mut().zip(constants) {
                    *value = value.add(constant);
                }
                for (column, value) in state.iter_mut().enumerate() {
                    if !(4..60).contains(&round) || column == 0 {
                        *value = value.square().square().mul(value);
                    }
                }
                state = parameters.mds.map(|row| {
                    row.iter()
                        .zip(&state)
                        .fold(PastaField::ZERO, |sum, (a, b)| sum.add(&a.mul(b)))
                });
            }
            assert_eq!(state[0].to_bytes(), case[64..96]);
        }
    }
    check(
        &super::PALLAS_BASE_T3,
        include_bytes!("../../tests/fixtures/poseidon-fp.bin"),
    );
    check(
        &super::PALLAS_SCALAR_T3,
        include_bytes!("../../tests/fixtures/poseidon-fq.bin"),
    );
}

const PALLAS_BASE_DIGEST: u128 = 0x38e9_acb9_6cdd_7395_996b_f0e8_a8f2_cacf;
const PALLAS_SCALAR_DIGEST: u128 = 0x2cba_8835_0552_681a_0f83_ea33_ccb4_049a;

/// Recomputes the digests after a verified table change:
/// `cargo test -p zakura-udon --features poseidon --lib poseidon::tests::print_digests -- --ignored --nocapture`.
#[test]
#[ignore = "prints the digests for pinning; run explicitly"]
fn print_digests() {
    println!("PALLAS_BASE_DIGEST = {:#034x}", digest(&PALLAS_BASE));
    println!("PALLAS_SCALAR_DIGEST = {:#034x}", digest(&PALLAS_SCALAR));
}
