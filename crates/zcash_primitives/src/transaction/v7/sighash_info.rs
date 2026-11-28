//! The `sighashInfo` field that accompanies every v7 signature.

use alloc::vec::Vec;
use corez::io::{self, Read, Write};

use zcash_protocol::encoding::{Array, CompactSize};

/// The field encoding of a `sighashInfo` that selects sighash variant 0, which has no
/// associated data: `sizeSighashInfo = 1` followed by `sighashVariant = 0`.
///
/// Variant 0 is the only sighash variant ZIP 248 defines for the bundle types it
/// registers, so the typed v7 bundles accept only this encoding and do not store it.
pub use orchard::bundle::commitments::V7_SIGHASH_INFO_V0 as SIGHASH_INFO_V0;

/// A `sighashInfo` field of any sighash variant.
///
/// The authorizing data of a registered bundle is decoded with every `sighashInfo` read
/// as this, so that its authorizing digest covers signatures of variants that network
/// upgrades may add within v7. The typed bundles then require [`SighashInfo::V0`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SighashInfo {
    /// Sighash variant 0 with no associated data: [`SIGHASH_INFO_V0`].
    V0,
    /// Any other `sighashInfo`, as its field encoding: `sizeSighashInfo` followed by
    /// `sighashInfo`.
    Other(Vec<u8>),
}

impl SighashInfo {
    /// Reads a `sighashInfo` field, which holds at least its `sighashVariant` byte.
    ///
    /// Variant 0 with no associated data is recognized without allocating, since every
    /// typed signature uses it.
    pub(crate) fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let len: usize = CompactSize::read_t(&mut reader)?;
        if len == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "a v7 sighashInfo must contain its sighash variant",
            ));
        }
        let mut variant = [0; 1];
        reader.read_exact(&mut variant)?;
        if len == 1 && variant == [SIGHASH_INFO_V0[1]] {
            return Ok(Self::V0);
        }
        let mut encoding = Vec::new();
        CompactSize::write(&mut encoding, len)?;
        encoding.extend_from_slice(&variant);
        // The rest grows only as the reader supplies it, so an untrusted length cannot
        // reserve more memory than the payload holds.
        encoding.extend(Array::read_bytes(reader, len - 1)?);
        Ok(Self::Other(encoding))
    }

    /// Returns the field encoding, which the authorizing digests hash.
    pub(crate) fn field_encoding(&self) -> &[u8] {
        match self {
            Self::V0 => &SIGHASH_INFO_V0,
            Self::Other(encoding) => encoding,
        }
    }

    /// Requires this to select sighash variant 0 with no associated data, the only
    /// `sighashInfo` that the typed v7 bundles represent.
    pub(crate) fn require_v0(&self) -> io::Result<()> {
        match self {
            Self::V0 => Ok(()),
            Self::Other(_) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "v7 signatures must use sighash variant 0 with no associated data",
            )),
        }
    }
}

/// A v7 signature field, `SaplingSignature` or `OrchardSignature`: a `sighashInfo` and
/// the 64-byte signature it accompanies.
#[derive(Clone, Debug)]
pub(crate) struct Signature {
    pub(crate) sighash_info: SighashInfo,
    pub(crate) signature: [u8; 64],
}

impl Signature {
    pub(crate) fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let sighash_info = SighashInfo::read(&mut reader)?;
        let mut signature = [0; 64];
        reader.read_exact(&mut signature)?;
        Ok(Self {
            sighash_info,
            signature,
        })
    }

    /// Returns the signature of a typed v7 bundle, which uses sighash variant 0.
    pub(crate) fn into_v0(self) -> io::Result<[u8; 64]> {
        self.sighash_info.require_v0()?;
        Ok(self.signature)
    }
}

/// Writes a `sighashInfo` field selecting sighash variant 0.
pub(crate) fn write_v0<W: Write>(mut writer: W) -> io::Result<()> {
    writer.write_all(&SIGHASH_INFO_V0)
}
