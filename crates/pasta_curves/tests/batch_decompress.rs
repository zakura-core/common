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

/// A wider differential sweep: x values next to 0 and p with both sign bits,
/// every single-bit and all-but-one-bit encoding, and a seeded mix of valid
/// points and arbitrary bytes, decoded in chunks that span every remainder
/// length.
macro_rules! sweep {
    ($affine:ty, $group:ty, $base:ty, $rng:expr) => {{
        let rng = $rng;
        let mut all: Vec<[u8; 32]> = Vec::new();
        for k in 0..512u64 {
            for x in [<$base>::from(k), -<$base>::from(k + 1)] {
                let mut bytes = x.to_repr();
                all.push(bytes);
                bytes[31] |= 0x80;
                all.push(bytes);
            }
        }
        for bit in 0..256 {
            let mut one = [0u8; 32];
            one[bit / 8] = 1 << (bit % 8);
            all.push(one);
            let mut all_but_one = [0xff; 32];
            all_but_one[bit / 8] &= !(1 << (bit % 8));
            all.push(all_but_one);
        }
        for _ in 0..4096 {
            all.push(<$group>::random(&mut *rng).to_bytes());
            let mut bytes = [0u8; 32];
            rng.fill_bytes(&mut bytes);
            all.push(bytes);
        }

        let mut valid = 0;
        for chunk in all.chunks(1013) {
            let got = <$affine>::batch_from_bytes(chunk.iter().copied());
            assert_eq!(got.len(), chunk.len());
            for (g, bytes) in got.iter().zip(chunk) {
                let e = <$affine>::from_bytes(bytes);
                assert_eq!(
                    bool::from(g.is_some()),
                    bool::from(e.is_some()),
                    "{bytes:02x?}"
                );
                if bool::from(e.is_some()) {
                    assert_eq!(g.unwrap(), e.unwrap(), "{bytes:02x?}");
                    valid += 1;
                }
            }
        }
        assert!(valid > 4096 && valid < all.len());
    }};
}

#[test]
fn batch_from_bytes_matches_from_bytes_sweep() {
    use ff::PrimeField;
    use pasta_curves::{Fp, Fq};

    let mut rng = XorShiftRng::from_seed([11; 16]);
    sweep!(pallas::Affine, pallas::Point, Fp, &mut rng);
    sweep!(vesta::Affine, vesta::Point, Fq, &mut rng);
}

/// `CurveAffine::batch_decode`, the generic entry point the verifiers use,
/// agrees with `from_bytes` too.
#[test]
fn curve_affine_batch_decode_matches_from_bytes() {
    use pasta_curves::arithmetic::CurveAffine;

    let mut rng = XorShiftRng::from_seed([9; 16]);
    let pallas_inputs = inputs::<pallas::Point>(&mut rng);
    for (got, bytes) in pallas::Affine::batch_decode(&pallas_inputs)
        .iter()
        .zip(&pallas_inputs)
    {
        let want = pallas::Affine::from_bytes(bytes);
        assert_eq!(bool::from(got.is_some()), bool::from(want.is_some()));
        if bool::from(want.is_some()) {
            assert_eq!(got.unwrap(), want.unwrap());
        }
    }
    let vesta_inputs = inputs::<vesta::Point>(&mut rng);
    for (got, bytes) in vesta::Affine::batch_decode(&vesta_inputs)
        .iter()
        .zip(&vesta_inputs)
    {
        let want = vesta::Affine::from_bytes(bytes);
        assert_eq!(bool::from(got.is_some()), bool::from(want.is_some()));
        if bool::from(want.is_some()) {
            assert_eq!(got.unwrap(), want.unwrap());
        }
    }
}
