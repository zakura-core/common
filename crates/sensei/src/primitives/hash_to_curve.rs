//! The Orchard Pallas XMD:BLAKE2b / simplified-SWU / degree-three isogeny map.
//! Constants and map conventions are pinned to the historical Pasta implementation.
use super::pallas::Point;
use udon::field::Fp;

const HASH_BYTES: usize = 64;
const BLOCK_BYTES: usize = 128;
const SUFFIX: &[u8] = b"-pallas_XMD:BLAKE2b_SSWU_RO_";
const ISO_A: Fp =
    udon::fp_hex!("0x18354a2eb0ea8c9c49be2d7258370742b74134581a27a59f92bb4b0b657a014b");
const ISO_B: Fp =
    udon::fp_hex!("0x00000000000000000000000000000000000000000000000000000000000004f1");
const ISOGENY_CONSTANTS: [Fp; 13] = [
    udon::fp_hex!("0x0e38e38e38e38e38e38e38e38e38e38e4081775473d8375b775f6034aaaaaaab"),
    udon::fp_hex!("0x3509afd51872d88e267c7ffa51cf412a0f93b82ee4b994958cf863b02814fb76"),
    udon::fp_hex!("0x17329b9ec525375398c7d7ac3d98fd13380af066cfeb6d690eb64faef37ea4f7"),
    udon::fp_hex!("0x1c71c71c71c71c71c71c71c71c71c71c8102eea8e7b06eb6eebec06955555580"),
    udon::fp_hex!("0x1d572e7ddc099cff5a607fcce0494a799c434ac1c96b6980c47f2ab668bcd71f"),
    udon::fp_hex!("0x325669becaecd5d11d13bf2a7f22b105b4abf9fb9a1fc81c2aa3af1eae5b6604"),
    udon::fp_hex!("0x1a12f684bda12f684bda12f684bda12f7642b01ad461bad25ad985b5e38e38e4"),
    udon::fp_hex!("0x1a84d7ea8c396c47133e3ffd28e7a09507c9dc17725cca4ac67c31d8140a7dbb"),
    udon::fp_hex!("0x3fb98ff0d2ddcadd303216cce1db9ff11765e924f745937802e2be87d225b234"),
    udon::fp_hex!("0x025ed097b425ed097b425ed097b425ed0ac03e8e134eb3e493e53ab371c71c4f"),
    udon::fp_hex!("0x0c02c5bcca0e6b7f0790bfb3506defb65941a3a4a97aa1b35a28279b1d1b42ae"),
    udon::fp_hex!("0x17033d3c60c68173573b3d7f7d681310d976bbfabbc5661d4d90ab820b12320a"),
    udon::fp_hex!("0x40000000000000000000000000000000224698fc094cf91b992d30ecfffffde5"),
];

/// Z = -13
const Z: Fp = udon::fp_hex!("0x40000000000000000000000000000000224698fc094cf91b992d30ecfffffff4");

/// `(F::ROOT_OF_UNITY.invert().unwrap() * z).sqrt().unwrap()`
const THETA: Fp =
    udon::fp_hex!("0x0f7bdb65814179b44647aef782d5cdc851f64fc4dc888857ca330bcc09ac318e");

pub(super) fn hash(domain: &str, message: &[u8]) -> Point {
    assert!(
        domain.len() + SUFFIX.len() < 256,
        "hash-to-curve domain is too long"
    );
    let empty = blake2b_simd::Params::new()
        .hash_length(HASH_BYTES)
        .to_state();
    let finish = |mut state: blake2b_simd::State| {
        state
            .update(domain.as_bytes())
            .update(SUFFIX)
            .update(&[(domain.len() + SUFFIX.len()) as u8])
            .finalize()
    };
    let mut first = empty.clone();
    first
        .update(&[0; BLOCK_BYTES])
        .update(message)
        .update(&[0, 128, 0]);
    let b0 = finish(first);
    let mut first = empty.clone();
    first.update(b0.as_bytes()).update(&[1]);
    let b1 = finish(first);
    let mut second = empty;
    let xor: [u8; HASH_BYTES] = core::array::from_fn(|i| b0.as_bytes()[i] ^ b1.as_bytes()[i]);
    second.update(&xor).update(&[2]);
    let b2 = finish(second);
    let [u0, u1] = [b1, b2].map(|digest| {
        let mut bytes = *digest.as_array();
        bytes.reverse();
        Fp::from_wide_bytes_reduced(&bytes)
    });
    isogeny(add(swu(u0), swu(u1)))
}

// Jacobian coordinates on the auxiliary isogenous curve. It has nonzero A;
// these coordinates are private to this map and never passed to Pallas kernels.
type IsoPoint = [Fp; 3];
fn swu(u: Fp) -> IsoPoint {
    let zu2 = Z.mul(&u.square());
    let ta = zu2.square().add(&zu2);
    let num_x1 = ISO_B.mul(&ta.add(&<Fp>::ONE));
    let div = ISO_A.mul(&if ta.is_zero() { Z } else { ta.neg() });
    let div2 = div.square();
    let div3 = div2.mul(&div);
    let numerator = num_x1
        .square()
        .add(&ISO_A.mul(&div2))
        .mul(&num_x1)
        .add(&ISO_B.mul(&div3));
    let (square, y1) = numerator.reduce().sqrt_ratio(&div3.reduce());
    let (num_x, mut y) = if square {
        (num_x1, y1.into_loose())
    } else {
        (zu2.mul(&num_x1), THETA.mul(&zu2).mul(&u).mul(&y1))
    };
    if u.is_odd() != y.is_odd() {
        y = y.neg();
    }
    [num_x.mul(&div), y.mul(&div3), div]
}
fn add([x1, y1, z1]: IsoPoint, [x2, y2, z2]: IsoPoint) -> IsoPoint {
    if z1.is_zero() {
        return [x2, y2, z2];
    }
    if z2.is_zero() {
        return [x1, y1, z1];
    }
    let z1s = z1.square();
    let z2s = z2.square();
    let u1 = x1.mul(&z2s);
    let u2 = x2.mul(&z1s);
    let s1 = y1.mul(&z2s).mul(&z2);
    let s2 = y2.mul(&z1s).mul(&z1);
    let h = u2.sub(&u1);
    let r = s2.sub(&s1);
    if h.is_zero() {
        if !r.is_zero() || y1.is_zero() {
            return [Fp::ZERO; 3];
        }
        let yy = y1.square();
        let yyyy = yy.square();
        let d = x1.mul(&yy).mul_by_4();
        let e = x1.square().triple().add(&ISO_A.mul(&z1s.square()));
        let x = e.square().sub(&d.double());
        return [
            x,
            e.mul(&d.sub(&x)).sub(&yyyy.mul_by_8()),
            y1.mul(&z1).double(),
        ];
    }
    let hh = h.square();
    let hhh = hh.mul(&h);
    let v = u1.mul(&hh);
    let x = r.square().sub(&hhh).sub(&v.double());
    [x, r.mul(&v.sub(&x)).sub(&s1.mul(&hhh)), z1.mul(&z2).mul(&h)]
}
fn isogeny([x, y, z]: IsoPoint) -> Point {
    let iso = ISOGENY_CONSTANTS;
    let z2 = z.square();
    let z3 = z2.mul(&z);
    let z4 = z2.square();
    let z6 = z3.square();
    let num_x = iso[0]
        .mul(&x)
        .add(&iso[1].mul(&z2))
        .mul(&x)
        .add(&iso[2].mul(&z4))
        .mul(&x)
        .add(&iso[3].mul(&z6));
    let div_x = z2
        .mul(&x)
        .add(&iso[4].mul(&z4))
        .mul(&x)
        .add(&iso[5].mul(&z6));
    let num_y = iso[6]
        .mul(&x)
        .add(&iso[7].mul(&z2))
        .mul(&x)
        .add(&iso[8].mul(&z4))
        .mul(&x)
        .add(&iso[9].mul(&z6))
        .mul(&y);
    let div_y = x
        .add(&iso[10].mul(&z2))
        .mul(&x)
        .add(&iso[11].mul(&z4))
        .mul(&x)
        .add(&iso[12].mul(&z6))
        .mul(&z3);
    let zo = div_x.mul(&div_y);
    let xo = num_x.mul(&div_y).mul(&zo);
    let yo = num_y.mul(&div_x).mul(&zo.square());
    Point::from_native(
        udon::curve::PallasProjective::from_jacobian(xo, yo, zo).expect("Pallas isogeny"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exceptional_swu_and_nonsquare_convention() {
        assert_eq!(THETA.square().mul(&Fp::SQRT_NONSQUARE).reduce(), Z.reduce());
        assert!(Z.neg().invert().unwrap().reduce().sqrt().is_none());
        let q = swu(Fp::ZERO);
        assert_eq!(
            q[1].square().reduce(),
            q[0].square()
                .mul(&q[0])
                .add(&ISO_A.mul(&q[0]).mul(&q[2].square().square()))
                .add(&ISO_B.mul(&q[2].square().square().mul(&q[2].square())))
                .reduce()
        );
        assert!(!isogeny(q).native().is_identity());
    }
}
