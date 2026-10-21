//! Polynomial artifacts derived from base-domain evaluations.
//!
//! `values` reconstructs fixed and sigma columns once per emission.
//! `coefficients` interpolates them; `cosets` expands them to the extended
//! coset. `basis` builds the instance and boundary Lagrange polynomials, and
//! `selectors` evaluates the shared selector recipe over the fixed cosets.
//! Encoders share coefficients and cosets through the emission's context;
//! individual artifact requests prepare only their own dependencies.

pub(crate) mod basis;
pub(crate) mod coefficients;
pub(crate) mod cosets;
pub(crate) mod selectors;
pub(crate) mod values;
