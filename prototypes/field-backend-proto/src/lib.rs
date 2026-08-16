//! Prototype backends for Pallas base-field (`Fp`) arithmetic on Apple
//! AArch64, benchmarked head-to-head in one binary:
//!
//! - **baseline / FFI**: a renamed copy of the vendored Semolina assembly
//!   (`src/proto.S`), called through `extern "C"` exactly like the real
//!   `aarch64-asm` backend in `pasta_curves`.
//! - **v1**: sparse-modulus portable Rust (CIOS specialized to
//!   `p[2] = 0`, `p[3] = 2^62`), fully inlinable.
//! - **v2**: the same Semolina arithmetic as inline `asm!` blocks with
//!   register operands and `options(pure, nomem, nostack)`, so LLVM
//!   register-allocates around them and can keep values in registers
//!   between field operations.
//! - **v3**: a hand-fused Jacobian `point_double_n` in assembly
//!   (`src/double_n.S`), field ops macro-inlined over a fixed stack frame —
//!   no per-field-op call or ABI traffic.
//!
//! All values are four little-endian `u64` limbs in Montgomery form
//! (R = 2^256) unless a function says otherwise.

#[cfg(feature = "v1")]
pub mod v1;
#[cfg(feature = "v2")]
pub mod v2;
#[cfg(feature = "v3")]
pub mod v3;

pub type Limbs = [u64; 4];

/// Pallas base field modulus limbs.
pub const P0: u64 = 0x992d30ed00000001;
pub const P1: u64 = 0x224698fc094cf91b;
pub const P3: u64 = 0x4000000000000000;
/// `-p^{-1} mod 2^64`.
pub const INV: u64 = 0x992d30ecffffffff;
pub const MODULUS: Limbs = [P0, P1, 0, P3];
/// R^2 = 2^512 mod p.
pub const R2: Limbs = [
    0x8c78ecb30000000f,
    0xd7d30dbd8b0de0e7,
    0x7797a99bc3c95d18,
    0x096d41af7b9cb714,
];
/// R = 2^256 mod p (the Montgomery form of 1).
pub const R1: Limbs = [
    0x34786d38fffffffd,
    0x992c350be41914ad,
    0xffffffffffffffff,
    0x3fffffffffffffff,
];

extern "C" {
    fn proto_mul_mont_pasta(
        out: *mut Limbs,
        lhs: *const Limbs,
        rhs: *const Limbs,
        modulus: *const Limbs,
        inv: u64,
    );
    fn proto_sqr_mont_pasta(out: *mut Limbs, value: *const Limbs, modulus: *const Limbs, inv: u64);
}

/// Baseline: Montgomery multiplication through the FFI boundary, identical
/// machine code to the vendored `pasta_curves` backend.
#[inline]
pub fn mul_ffi(a: &Limbs, b: &Limbs) -> Limbs {
    let mut out = Limbs::default();
    unsafe { proto_mul_mont_pasta(&mut out, a, b, &MODULUS, INV) };
    out
}

/// Baseline: Montgomery squaring through the FFI boundary.
#[inline]
pub fn sqr_ffi(a: &Limbs) -> Limbs {
    let mut out = Limbs::default();
    unsafe { proto_sqr_mont_pasta(&mut out, a, &MODULUS, INV) };
    out
}

/// Converts canonical little-endian limbs into Montgomery form.
pub fn to_mont(a: &Limbs) -> Limbs {
    mul_ffi(a, &R2)
}

/// Converts Montgomery-form limbs back to canonical little-endian limbs.
pub fn from_mont(a: &Limbs) -> Limbs {
    mul_ffi(a, &[1, 0, 0, 0])
}

// --- portable primitive helpers -------------------------------------------

#[inline(always)]
pub(crate) const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let t = (a as u128) + (b as u128) * (c as u128) + (carry as u128);
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
pub(crate) const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let t = (a as u128) + (b as u128) + (carry as u128);
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
pub(crate) const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let t = (a as u128).wrapping_sub((b as u128) + (borrow as u128));
    (t as u64, ((t >> 64) as u64) & 1)
}

/// One conditional subtraction of p; valid for inputs below 2p.
#[inline(always)]
pub(crate) const fn reduce_once(t: Limbs) -> Limbs {
    let (r0, brw) = sbb(t[0], P0, 0);
    let (r1, brw) = sbb(t[1], P1, brw);
    let (r2, brw) = sbb(t[2], 0, brw);
    let (r3, brw) = sbb(t[3], P3, brw);
    // brw = 1 means t < p: keep t.
    let keep = brw.wrapping_neg();
    [
        (t[0] & keep) | (r0 & !keep),
        (t[1] & keep) | (r1 & !keep),
        (t[2] & keep) | (r2 & !keep),
        (t[3] & keep) | (r3 & !keep),
    ]
}

// --- cheap modular ops (shared by every composed doubling) -----------------

#[inline(always)]
pub fn add_mod(a: &Limbs, b: &Limbs) -> Limbs {
    let (d0, c) = adc(a[0], b[0], 0);
    let (d1, c) = adc(a[1], b[1], c);
    let (d2, c) = adc(a[2], b[2], c);
    let (d3, _) = adc(a[3], b[3], c); // sum < 2p < 2^256: no carry out
    reduce_once([d0, d1, d2, d3])
}

#[inline(always)]
pub fn dbl_mod(a: &Limbs) -> Limbs {
    add_mod(a, a)
}

#[inline(always)]
pub fn sub_mod(a: &Limbs, b: &Limbs) -> Limbs {
    let (d0, brw) = sbb(a[0], b[0], 0);
    let (d1, brw) = sbb(a[1], b[1], brw);
    let (d2, brw) = sbb(a[2], b[2], brw);
    let (d3, brw) = sbb(a[3], b[3], brw);
    // On borrow, add p back.
    let mask = brw.wrapping_neg();
    let (r0, c) = adc(d0, P0 & mask, 0);
    let (r1, c) = adc(d1, P1 & mask, c);
    let (r2, c) = adc(d2, 0, c);
    let (r3, _) = adc(d3, P3 & mask, c);
    [r0, r1, r2, r3]
}

/// Jacobian point doubling (dbl-2009-l, a = 0) composed from a
/// multiplication and a squaring primitive. Mirrors
/// `pasta_curves::curves` exactly; the identity (Z = 0) propagates
/// automatically because Z3 = 2·Y·Z.
#[inline(always)]
pub fn double_jacobian(
    x: &mut Limbs,
    y: &mut Limbs,
    z: &mut Limbs,
    mul: impl Fn(&Limbs, &Limbs) -> Limbs,
    sqr: impl Fn(&Limbs) -> Limbs,
) {
    let b = sqr(y);
    let c = sqr(&b);
    let t = add_mod(x, &b);
    let a = sqr(x);
    let z3 = dbl_mod(&mul(y, z));
    let t2 = sqr(&t);
    let d = dbl_mod(&sub_mod(&sub_mod(&t2, &a), &c));
    let e = add_mod(&dbl_mod(&a), &a);
    let f = sqr(&e);
    let x3 = sub_mod(&sub_mod(&f, &d), &d);
    let y3 = sub_mod(
        &mul(&e, &sub_mod(&d, &x3)),
        &dbl_mod(&dbl_mod(&dbl_mod(&c))),
    );
    *x = x3;
    *y = y3;
    *z = z3;
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::{Field, PrimeField};
    use group::{Curve, Group};
    use group::prime::PrimeCurveAffine;
    use pasta_curves::arithmetic::CurveAffine;
    use pasta_curves::{pallas, Fp};
    use rand::SeedableRng;

    fn fp_to_canonical(f: &Fp) -> Limbs {
        let repr = f.to_repr();
        let mut l = [0u64; 4];
        for i in 0..4 {
            l[i] = u64::from_le_bytes(repr[8 * i..8 * i + 8].try_into().unwrap());
        }
        l
    }

    fn random_canonical(rng: &mut impl rand::RngCore) -> (Fp, Limbs) {
        let f = Fp::random(rng);
        let l = fp_to_canonical(&f);
        (f, l)
    }

    #[test]
    fn field_variants_match_pasta() {
        let mut rng = rand_xorshift::XorShiftRng::from_seed([7; 16]);

        let mut cases: Vec<(Fp, Limbs)> = vec![
            (Fp::ZERO, [0; 4]),
            (Fp::ONE, [1, 0, 0, 0]),
            (-Fp::ONE, [P0 - 1, P1, 0, P3]),
        ];
        for _ in 0..1024 {
            cases.push(random_canonical(&mut rng));
        }

        for (fa, a) in &cases {
            let am = to_mont(a);

            // Squaring across all variants.
            let expected_sq = fp_to_canonical(&(fa * fa));
            let mut sqrs: Vec<(&str, Limbs)> = vec![("ffi", sqr_ffi(&am))];
            #[cfg(feature = "v1")]
            sqrs.push(("v1", v1::sqr(&am)));
            #[cfg(feature = "v2")]
            sqrs.push(("v2", v2::sqr(&am)));
            for (name, got) in sqrs {
                assert_eq!(from_mont(&got), expected_sq, "sqr mismatch: {name}");
            }

            for (fb, b) in cases.iter().take(16) {
                let bm = to_mont(b);
                let expected = fp_to_canonical(&(fa * fb));
                let ffi = mul_ffi(&am, &bm);
                assert_eq!(from_mont(&ffi), expected, "ffi mul mismatch");
                // All variants canonicalize, so the Montgomery limbs must
                // agree exactly, not just modulo p.
                #[cfg(feature = "v1")]
                assert_eq!(v1::mul(&am, &bm), ffi, "v1 mul limbs differ from ffi");
                #[cfg(feature = "v2")]
                assert_eq!(v2::mul(&am, &bm), ffi, "v2 mul limbs differ from ffi");
            }
        }
    }

    fn generator_jacobian() -> ([u64; 4], [u64; 4], [u64; 4]) {
        let g = pallas::Affine::generator();
        let coords = g.coordinates().unwrap();
        let x = to_mont(&fp_to_canonical(coords.x()));
        let y = to_mont(&fp_to_canonical(coords.y()));
        (x, y, R1)
    }

    /// Checks (X : Y : Z) equals the affine point, projectively:
    /// X = x·Z², Y = y·Z³.
    fn assert_matches_affine(x: &Limbs, y: &Limbs, z: &Limbs, p: &pallas::Point) {
        let aff = p.to_affine();
        let coords = aff.coordinates().unwrap();
        let xa = to_mont(&fp_to_canonical(coords.x()));
        let ya = to_mont(&fp_to_canonical(coords.y()));
        let z2 = sqr_ffi(z);
        let z3 = mul_ffi(&z2, z);
        assert_eq!(*x, mul_ffi(&xa, &z2), "X != x*Z^2");
        assert_eq!(*y, mul_ffi(&ya, &z3), "Y != y*Z^3");
    }

    #[test]
    fn doubling_variants_match_pasta() {
        for n in [1usize, 2, 3, 7, 129] {
            let (gx, gy, gz) = generator_jacobian();

            // Composed variants.
            let mut variants: Vec<(&str, Limbs, Limbs, Limbs)> = Vec::new();
            let mut backends: Vec<(&str, fn(&Limbs, &Limbs) -> Limbs, fn(&Limbs) -> Limbs)> =
                vec![("ffi", mul_ffi, sqr_ffi)];
            #[cfg(feature = "v1")]
            backends.push(("v1", v1::mul, v1::sqr));
            #[cfg(feature = "v2")]
            backends.push(("v2", v2::mul, v2::sqr));
            for (name, mulf, sqrf) in backends {
                let (mut x, mut y, mut z) = (gx, gy, gz);
                for _ in 0..n {
                    double_jacobian(&mut x, &mut y, &mut z, mulf, sqrf);
                }
                variants.push((name, x, y, z));
            }

            // Fused assembly.
            #[cfg(feature = "v3")]
            {
                let mut xyz = [0u64; 12];
                xyz[0..4].copy_from_slice(&gx);
                xyz[4..8].copy_from_slice(&gy);
                xyz[8..12].copy_from_slice(&gz);
                v3::double_n(&mut xyz, n);
                variants.push((
                    "v3",
                    xyz[0..4].try_into().unwrap(),
                    xyz[4..8].try_into().unwrap(),
                    xyz[8..12].try_into().unwrap(),
                ));
            }

            // Ground truth from pasta_curves.
            let mut expected = pallas::Point::generator();
            for _ in 0..n {
                expected = expected.double();
            }

            let (_, x0, y0, z0) = variants[0];
            for (name, x, y, z) in &variants {
                assert_eq!((x, y, z), (&x0, &y0, &z0), "{name} limbs diverge at n={n}");
                assert_matches_affine(x, y, z, &expected);
            }
        }
    }

    #[test]
    fn doubling_identity_passthrough() {
        // Z = 0 (the identity) must stay the identity in every variant.
        let (gx, gy, _) = generator_jacobian();
        let zero = [0u64; 4];

        let (mut x, mut y, mut z) = (gx, gy, zero);
        double_jacobian(&mut x, &mut y, &mut z, mul_ffi, sqr_ffi);
        assert_eq!(z, zero);

        #[cfg(feature = "v3")]
        {
            let mut xyz = [0u64; 12];
            xyz[0..4].copy_from_slice(&gx);
            xyz[4..8].copy_from_slice(&gy);
            v3::double_n(&mut xyz, 3);
            assert_eq!(&xyz[8..12], &zero);
        }
    }
}
