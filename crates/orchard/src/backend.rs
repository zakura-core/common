//! Private access to Orchard's legacy implementation dependencies.
#![allow(unused_imports)]
pub(crate) use orchard_legacy::pasta_curves::pallas;
pub(crate) use orchard_legacy::{ff, group, pasta_curves, poseidon, reddsa, sinsemilla};
#[cfg(feature = "circuit")]
pub(crate) use orchard_legacy::{halo2_gadgets, halo2_proofs};

pub(crate) mod prelude {
    pub(crate) use orchard_legacy::{
        ff::{Field as _, FromUniformBytes as _, PrimeField as _, PrimeFieldBits as _},
        group::{Curve as _, CurveAffine as _, Group as _, GroupEncoding as _},
        pasta_curves::arithmetic::{CurveAffine as _, CurveExt as _},
    };
}
