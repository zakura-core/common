//! Shared support code for Sensei's integration harnesses.
//!
//! Everything here is written purely against the crate's public API so that
//! the harnesses including it remain ordinary external consumers of the
//! library, without importing its private test scaffolding.
//!
//! The "Oracle independence" section in `crates/sensei/src/native/mod.rs`
//! records the boundary: fixture decoding stays separate from unit-test support,
//! while public field/point decoding is shared. This source cross-reference also
//! works for external harnesses that cannot link to private library items.

// Each integration test needs a different subset of these purpose-specific
// helpers: verification uses only the RNG. Keep dead-code allowances on those
// helper boundaries.
#[allow(dead_code)]
mod cursor;
#[allow(dead_code)]
mod iwpr;
#[allow(dead_code)]
mod rng;

// Preserve the facade for all harnesses without requiring each binary to use
// every export. Imports inside the child modules are limited to their purpose.
#[allow(unused_imports)]
pub use cursor::{Cursor, FIELD_SIZE};
#[allow(unused_imports)]
pub use iwpr::{
    ACTION_SIZE, HEADER_SIZE, MAGIC, MERKLE_DEPTH, PRIVATE_WITNESS_SIZE, PUBLIC_STATEMENT_SIZE,
    REQUEST_FORMAT_VERSION, TARGET_FORMAT_VERSION, TARGET_ID,
};
#[allow(unused_imports)]
#[cfg(feature = "prover")]
pub use iwpr::{decode_actions, decode_request};
#[allow(unused_imports)]
pub use rng::SplitMix64;
