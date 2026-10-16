//! Pin both backends' copies against their independent domain derivation and arithmetic.
use super::*;
#[cfg(feature = "backend-halo2")]
use crate::backend::prelude::*;
use crate::backend::{
    pallas,
    sinsemilla::{CommitDomain, HashDomain},
};
use crate::constants::{
    fixed_bases::{COMMIT_IVK_PERSONALIZATION, NOTE_COMMITMENT_PERSONALIZATION},
    sinsemilla::MERKLE_CRH_PERSONALIZATION,
};
use proptest::prelude::*;

#[test]
// Nodes in the Merkle tree are Pallas base field elements.
fn l_orchard_merkle() {
    assert_eq!(super::L_ORCHARD_MERKLE, pallas::Base::NUM_BITS as usize);
}

proptest! {
    #[test]
    fn lebs2ip_k_round_trip(int in 0usize..(1 << K)) {
        assert_eq!(lebs2ip_k(&i2lebsp_k(int)) as usize, int);

        assert_eq!(lebs2ip_k(&i2lebsp_k(0)) as usize, 0);
        assert_eq!(lebs2ip_k(&i2lebsp_k((1 << K) - 1)) as usize, (1 << K) - 1);
    }

    #[test]
    fn i2lebsp_k_round_trip(bitstring in any::<[bool; K]>()) {
        assert_eq!(i2lebsp_k(lebs2ip_k(&bitstring) as usize), bitstring);

        let bitstring = [false; K];
        assert_eq!(i2lebsp_k(lebs2ip_k(&bitstring) as usize), bitstring);

        let bitstring = [true; K];
        assert_eq!(i2lebsp_k(lebs2ip_k(&bitstring) as usize), bitstring);
    }
}

#[test]
fn q_note_commitment_m() {
    let domain = CommitDomain::new(NOTE_COMMITMENT_PERSONALIZATION);
    let point = domain.Q();
    let coords = point.to_affine().coordinates().unwrap();

    assert_eq!(
        *coords.x(),
        pallas::Base::from_repr(Q_NOTE_COMMITMENT_M_GENERATOR.0).unwrap()
    );
    assert_eq!(
        *coords.y(),
        pallas::Base::from_repr(Q_NOTE_COMMITMENT_M_GENERATOR.1).unwrap()
    );
}

#[test]
fn q_commit_ivk_m() {
    let domain = CommitDomain::new(COMMIT_IVK_PERSONALIZATION);
    let point = domain.Q();
    let coords = point.to_affine().coordinates().unwrap();

    assert_eq!(
        *coords.x(),
        pallas::Base::from_repr(Q_COMMIT_IVK_M_GENERATOR.0).unwrap()
    );
    assert_eq!(
        *coords.y(),
        pallas::Base::from_repr(Q_COMMIT_IVK_M_GENERATOR.1).unwrap()
    );
}

#[test]
fn q_merkle_crh() {
    let domain = HashDomain::new(MERKLE_CRH_PERSONALIZATION);
    let point = domain.Q();
    let coords = point.to_affine().coordinates().unwrap();

    assert_eq!(
        *coords.x(),
        pallas::Base::from_repr(Q_MERKLE_CRH.0).unwrap()
    );
    assert_eq!(
        *coords.y(),
        pallas::Base::from_repr(Q_MERKLE_CRH.1).unwrap()
    );
}

#[test]
fn inv_two_pow_k() {
    let two_pow_k = pallas::Base::from(1u64 << K);
    let inv_two_pow_k = pallas::Base::from_repr(INV_TWO_POW_K).unwrap();

    assert_eq!(two_pow_k * inv_two_pow_k, pallas::Base::one());
}
