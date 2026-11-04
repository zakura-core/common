//! `batch_from_bytes` must agree with `from_bytes` on every input.
#![cfg(all(feature = "sqrt-table", feature = "alloc"))]

use group::{Group, GroupEncoding};
use pasta_curves::{pallas, vesta};
use rand::{Rng, SeedableRng};
use rand_xorshift::XorShiftRng;

fn inputs<G: Group + GroupEncoding<Repr = [u8; 32]>>(rng: &mut XorShiftRng) -> Vec<[u8; 32]> {
    let mut v = Vec::new();
    for _ in 0..40 {
        v.push(G::random(&mut *rng).to_bytes());
    }
    // Arbitrary bytes: about half have a non-square x^3 + 5, and some are
    // non-canonical.
    for _ in 0..40 {
        let mut b = [0u8; 32];
        rng.fill_bytes(&mut b);
        v.push(b);
    }
    v.push(G::identity().to_bytes());
    // x = 0 with the sign bit set is not the identity encoding.
    let mut x0_sign = [0u8; 32];
    x0_sign[31] = 0x80;
    v.push(x0_sign);
    v.push([0xff; 32]);
    let mut max = [0xff; 32];
    max[31] = 0x7f;
    v.push(max);
    v
}

macro_rules! check {
    ($affine:ty, $group:ty, $rng:expr) => {{
        let mut all = inputs::<$group>($rng);
        let expected: Vec<_> = all.iter().map(<$affine>::from_bytes).collect();
        let valid = expected.iter().filter(|e| bool::from(e.is_some())).count();
        assert!(valid > 40 && valid < all.len());
        // Every chunk shape: full chunks of eight plus each remainder length,
        // with special inputs at different positions.
        for len in (0..=17).chain([all.len()]) {
            for rotation in [0, 3, 80] {
                all.rotate_left(rotation);
                let expected: Vec<_> = all.iter().map(<$affine>::from_bytes).collect();
                let got = <$affine>::batch_from_bytes(all[..len].iter().copied());
                assert_eq!(got.len(), len);
                for (g, e) in got.iter().zip(&expected[..len]) {
                    assert_eq!(bool::from(g.is_some()), bool::from(e.is_some()));
                    if bool::from(e.is_some()) {
                        assert_eq!(g.unwrap(), e.unwrap());
                    }
                }
            }
        }
    }};
}

#[test]
fn batch_from_bytes_matches_from_bytes() {
    let mut rng = XorShiftRng::from_seed([7; 16]);
    check!(pallas::Affine, pallas::Point, &mut rng);
    check!(vesta::Affine, vesta::Point, &mut rng);
}
