//! I/O types selected by the crate's standard-library feature.

#[cfg(all(not(feature = "std"), not(feature = "no-std-io")))]
compile_error!("enable either `std` or `no-std-io` for I/O support");

// Some key-feature selections do not use an I/O type.
#[allow(unused_imports)]
#[cfg(feature = "std")]
pub(crate) use std::io::*;

#[allow(unused_imports)]
#[cfg(all(not(feature = "std"), feature = "no-std-io"))]
pub(crate) use corez::io::*;
