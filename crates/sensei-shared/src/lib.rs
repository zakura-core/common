//! Shared description of the fixed post-NU6.3 Ironwood Action circuit.
//!
//! [`sensei-artifacts`](../zakura_sensei_artifacts/index.html) generates data on
//! the host, [`sensei-macros`](../zakura_sensei_macros/index.html) generates
//! executable Rust during macro expansion, and
//! [Sensei](../zakura_sensei/index.html#crate-map) consumes both. This crate
//! defines their circuit facts, expression recipes, stored record layouts, and
//! reconstruction routines. It has no witness or randomness inputs.
//!
//! This `no_std` + `alloc` crate is a dependency of all three consumers and
//! depends on none of them. The host generators and Sensei's build script use
//! host copies; Sensei's primitives and proof runtime use the target copy.
//!
//! Start with [`dimensions`] for domain sizes, then follow the relevant data:
//!
//! - [`fixed_columns`] describes and reconstructs the 29 fixed columns.
//! - [`permutation`] expands the sigma map into sigma and identity evaluations.
//! - [`generators`] and [`fixed_bases`] define the Pallas points and window tables.
//! - [`regions`] maps synthesis-region IDs to absolute rows.
//! - [`queries`] defines query order and the fused evaluator's query frame;
//!   [`selectors`] prepares its fixed-only selector values.
//! - [`records`] defines the exact layouts written and embedded through `bento`.
//! - [`commitment_tables`] and [`fft`] describe preparation policies and table
//!   layouts shared by host generation and target preparation.
//! - [`programs`] defines the gate and lookup recipes over an arithmetic algebra;
//!   [`expressions`] provides their trees and analyses, and [`constants`] their
//!   shared field constants.
//!
//! Follow [Sensei's crate map](../zakura_sensei/index.html#crate-map) for its
//! standalone primitives, signatures, native proof runtime, and the expression
//! reference's boundary. The generator crates linked above own artifact
//! serialization and raw-input validation, and expression lowering and token
//! emission, respectively.
#![no_std]
#![deny(unsafe_code)]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
// Preserve the imported `chunks_exact` code, as in Udon. The pinned
// toolchain's Clippy predates this lint (introduced in 1.98).
#![allow(unknown_lints)]
#![allow(clippy::chunks_exact_to_as_chunks)]
extern crate alloc;

pub mod commitment_tables;
pub mod constants;
pub mod dimensions;
pub mod expressions;
pub mod fft;
pub mod fixed_bases;
pub mod fixed_columns;
pub mod generators;
pub mod permutation;
pub mod programs;
pub mod queries;
pub mod records;
pub mod regions;
pub mod selectors;

// Circuit descriptions also exposed at the root for their consumers.
pub use dimensions::{
    ADVICE_COLUMNS, BLINDING_FACTORS, CONSTRAINT_DEGREE, EXTENDED_K, EXTENDED_N, FIXED_COLUMNS,
    INSTANCE_COLUMNS, INSTANCE_VALUE_COUNT, K, MERKLE_DEPTH, N, PERMUTATION_CHUNK_LEN,
    PERMUTATION_COLUMN_COUNT, PERMUTATION_SETS, QUOTIENT_PIECES, USABLE_ROWS_END,
};
pub use fixed_columns as fixed_layout;
pub use fixed_columns::build_fixed_values;
pub use permutation::sigma_lagrange_values;
pub use records::{
    PreparedPointsFile, PrimitivePointsFile, RowAssignment, SrsPointsFile, WindowTableEntry,
};
