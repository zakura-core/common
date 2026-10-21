//! The pinned auxiliary Vesta generators of the polynomial commitment scheme.
//!
//! Like the Orchard fixed bases in [`generators`](sensei_shared::generators), these
//! two single points are circuit-description source rather than raw data:
//! canonical coordinates checked against the curve equation at compile time,
//! held as ready [`VestaAffine`] values in the at-rest representation. `W`
//! blinds every polynomial commitment; `U` is the auxiliary generator of the
//! inner-product argument. Both are protocol values fixed by the historical
//! parameter derivation, the counterpart of the raw-data SRS vector.

use udon::{curve::VestaAffine, fq_hex};

/// The pinned commitment blinding generator `W`.
pub(super) const BLIND_GENERATOR: VestaAffine = udon::vesta_affine!(
    fq_hex!("0x2bbc94ef7b22aebef24f9a4b0cc1831882548b605171366017d45c3e6fd92075"),
    fq_hex!("0x082b801a6e176239943bfb759fb02138f47a5c8cc4aa7fa0af559fde4e3abd97"),
);

/// The pinned IPA auxiliary generator `U`.
pub(super) const IPA_GENERATOR: VestaAffine = udon::vesta_affine!(
    fq_hex!("0x17a8b1830ad3ba49f240c0d0244f6911f6ac5997bba0d5c7cc61bffddcc49d37"),
    fq_hex!("0x2df4dd8b1be11f9db0176cf4cd0e52ff5528f693211cb7212bf6acd3327782cf"),
);
