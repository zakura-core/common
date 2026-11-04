//! Canonical public-statement slot order.

/// The note-commitment tree anchor.
pub const ANCHOR: usize = 0;
/// Net value commitment, affine `x`.
pub const CV_NET_X: usize = 1;
/// Net value commitment, affine `y`.
pub const CV_NET_Y: usize = 2;
/// The spent note's nullifier.
pub const NF_OLD: usize = 3;
/// Randomized spend validating key, affine `x`.
pub const RK_X: usize = 4;
/// Randomized spend validating key, affine `y`.
pub const RK_Y: usize = 5;
/// The new note's extracted commitment.
pub const CMX: usize = 6;
/// Whether the spend is enabled (0 or 1).
pub const ENABLE_SPEND: usize = 7;
/// Whether the output is enabled (0 or 1).
pub const ENABLE_OUTPUT: usize = 8;
/// Whether the cross-address restriction is enforced (0 or 1).
pub const DISABLE_CROSS_ADDRESS: usize = 9;
/// Number of public inputs; the populated instance prefix.
pub const COUNT: usize = DISABLE_CROSS_ADDRESS + 1;

const _: () = assert!(COUNT == sensei_shared::INSTANCE_VALUE_COUNT);
