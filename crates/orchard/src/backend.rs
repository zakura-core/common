//! Private compile-time arithmetic selection.
#![allow(unused_imports)]
#[cfg(feature = "backend-halo2")]
pub(crate) use orchard_legacy::pasta_curves::pallas;
#[cfg(feature = "backend-halo2")]
pub(crate) use orchard_legacy::{ff, group, pasta_curves, poseidon, reddsa, sinsemilla};
#[cfg(all(
    feature = "backend-halo2",
    any(feature = "prover", feature = "verifier")
))]
pub(crate) use orchard_legacy::{halo2_gadgets, halo2_proofs};
#[cfg(feature = "backend-sensei")]
pub(crate) use sensei::primitives::pallas;

pub(crate) mod prelude {
    #[cfg(feature = "backend-halo2")]
    pub(crate) use orchard_legacy::{
        ff::{Field as _, FromUniformBytes as _, PrimeField as _},
        group::{Curve as _, CurveAffine as _, Group as _, GroupEncoding as _},
        pasta_curves::arithmetic::{CurveAffine as _, CurveExt as _},
    };
}

#[cfg(feature = "backend-sensei")]
pub(crate) use sensei::primitives::sinsemilla;

/// Normalize the scalar libraries' boolean return types at the private boundary.
pub(crate) fn scalar_is_zero(scalar: &pallas::Scalar) -> bool {
    #[cfg(feature = "backend-sensei")]
    {
        scalar.is_zero()
    }
    #[cfg(feature = "backend-halo2")]
    {
        use prelude::*;
        bool::from(scalar.is_zero())
    }
}
