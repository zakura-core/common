//! Structural decoding errors.

use core::fmt;

/// The reason a byte string is not a structurally valid transaction encoding.
///
/// Every variant describes a problem with the encoding itself. None of them
/// reports a cryptographic or contextual consensus failure: this crate never
/// checks those (see the crate documentation).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
// Each variant's doc comment describes its fields.
#[allow(missing_docs)]
pub enum DecodeError {
    /// The input ended while reading `field`; `needed` more bytes were required.
    Truncated { field: &'static str, needed: usize },
    /// A CompactSize used a longer encoding than its value requires.
    NonCanonicalCompactSize { field: &'static str },
    /// A CompactSize exceeded the protocol maximum of `0x02000000`.
    CompactSizeTooLarge { field: &'static str, value: u64 },
    /// A collection's declared element count cannot fit in the remaining input.
    CountExceedsInput { field: &'static str, count: usize },
    /// The header is not one of the supported version/overwintered/group combinations.
    UnsupportedVersion { header: u32, version_group_id: Option<u32> },
    /// The embedded consensus branch ID is not a known branch.
    UnknownBranchId(u32),
    /// The transaction version is not permitted under the embedded branch ID.
    VersionNotValidInBranch { version: u32, branch_id: u32 },
    /// An amount is outside the range the protocol allows for `field`.
    ValueOutOfRange { field: &'static str },
    /// A shielded pool has descriptions but is not active under the embedded branch.
    PoolNotActive { pool: &'static str },
    /// A Sapling value balance is non-zero although the bundle has no spends or outputs.
    NonZeroBalanceWithoutDescriptions,
    /// An Orchard-protocol flags byte sets reserved bits for its pool.
    InvalidFlags { pool: &'static str, flags: u8 },
    /// An Orchard-protocol proof does not have the canonical length for its action count.
    InvalidProofLength {
        pool: &'static str,
        expected: usize,
        actual: usize,
    },
    /// `parse_exact` found bytes after the end of the transaction.
    TrailingBytes { count: usize },
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecodeError::Truncated { field, needed } => {
                write!(f, "input truncated in {field}: {needed} more bytes needed")
            }
            DecodeError::NonCanonicalCompactSize { field } => {
                write!(f, "non-canonical CompactSize in {field}")
            }
            DecodeError::CompactSizeTooLarge { field, value } => {
                write!(f, "CompactSize {value} in {field} exceeds 0x02000000")
            }
            DecodeError::CountExceedsInput { field, count } => {
                write!(f, "{field} count {count} cannot fit in the remaining input")
            }
            DecodeError::UnsupportedVersion {
                header,
                version_group_id,
            } => write!(
                f,
                "unsupported transaction header {header:#010x} with version group {version_group_id:?}"
            ),
            DecodeError::UnknownBranchId(id) => write!(f, "unknown consensus branch ID {id:#010x}"),
            DecodeError::VersionNotValidInBranch { version, branch_id } => write!(
                f,
                "transaction version {version} is not valid under branch {branch_id:#010x}"
            ),
            DecodeError::ValueOutOfRange { field } => write!(f, "{field} is out of range"),
            DecodeError::PoolNotActive { pool } => {
                write!(f, "{pool} descriptions are not allowed under this branch")
            }
            DecodeError::NonZeroBalanceWithoutDescriptions => write!(
                f,
                "Sapling value balance is non-zero without spends or outputs"
            ),
            DecodeError::InvalidFlags { pool, flags } => {
                write!(f, "invalid {pool} flags byte {flags:#04x}")
            }
            DecodeError::InvalidProofLength {
                pool,
                expected,
                actual,
            } => write!(
                f,
                "{pool} proof is {actual} bytes; the canonical length is {expected}"
            ),
            DecodeError::TrailingBytes { count } => {
                write!(f, "{count} trailing bytes after the transaction")
            }
        }
    }
}

impl core::error::Error for DecodeError {}
