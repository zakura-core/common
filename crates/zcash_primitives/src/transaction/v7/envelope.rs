//! The bundle-agnostic v7 encoding and its parsing rules.
//!
//! Everything here can be parsed without knowing any payment protocol: bundle payloads
//! stay opaque byte strings. Every [`Envelope`], whether constructed or decoded, satisfies
//! the ZIP 248 "Parsing Rules" and the nonzero `nConsensusBranchId` of its field table:
//! [`Envelope::new`] checks the map rules and the branch ID, and the type of
//! [`ValuePoolDelta::value`] holds the nonzero-delta rule.

use alloc::{collections::BTreeMap, vec::Vec};
use core::{fmt, num::NonZeroI64};
use corez::io::{self, Read, Write};

use zcash_protocol::{
    constants::{V7_TX_VERSION, V7_VERSION_GROUP_ID},
    encoding::{CompactSize, MAX_COMPACT_SIZE, Vector},
};

use super::registry::{BundleId, BundleType, BundleVariant};
use crate::encoding::{ReadBytesExt, WriteBytesExt};

/// The `header` field of every v7 transaction: `fOverwintered` and version 7.
pub(crate) const V7_HEADER: u32 = (1 << 31) | V7_TX_VERSION;

/// The common transaction fields of a v7 transaction that follow the version group ID.
///
/// The consensus branch ID is kept as the raw encoded value, so that a transaction for
/// an epoch this library does not know can still be parsed, and identified from the
/// digests of its bundles.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Header {
    /// `nConsensusBranchId`, which must be nonzero.
    pub consensus_branch_id: u32,
    /// `lock_time`.
    pub lock_time: u32,
    /// `nExpiryHeight`.
    pub expiry_height: u32,
}

impl Header {
    fn read_after_version<R: Read>(mut reader: R) -> io::Result<Self> {
        Ok(Self {
            consensus_branch_id: reader.read_u32_le()?,
            lock_time: reader.read_u32_le()?,
            expiry_height: reader.read_u32_le()?,
        })
    }

    /// Writes the encoded common transaction fields, which T.1 `header_digest` hashes.
    pub(crate) fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_u32_le(V7_HEADER)?;
        writer.write_u32_le(V7_VERSION_GROUP_ID)?;
        writer.write_u32_le(self.consensus_branch_id)?;
        writer.write_u32_le(self.lock_time)?;
        writer.write_u32_le(self.expiry_height)
    }
}

/// An entry of `mValuePoolDeltas`: a bundle's net change to the transparent transaction
/// value pool, in zatoshis.
///
/// A positive value adds to the pool and a negative value removes from it. Zero values
/// are not representable, because the encoding elides them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValuePoolDelta {
    /// The bundle the delta belongs to.
    pub bundle: BundleId,
    /// The nonzero change to the transparent transaction value pool.
    pub value: NonZeroI64,
}

impl ValuePoolDelta {
    fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let bundle = read_bundle_id(&mut reader)?;
        let mut value = [0; 8];
        reader.read_exact(&mut value)?;
        let value = NonZeroI64::new(i64::from_le_bytes(value))
            .ok_or_else(|| invalid(EnvelopeError::ZeroValuePoolDelta(bundle.bundle_type)))?;
        Ok(Self { bundle, value })
    }

    pub(crate) fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        write_bundle_id(&mut writer, self.bundle)?;
        writer.write_all(&self.value.get().to_le_bytes())
    }
}

/// An entry of `mEffectBundles` or `mAuthBundles`: a bundle's effecting or authorizing
/// data, as an opaque payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BundleData {
    /// The bundle the payload belongs to.
    pub bundle: BundleId,
    /// `vBundleData`.
    pub data: Vec<u8>,
}

impl BundleData {
    /// Decodes this payload with `decode`, which must consume exactly the declared length.
    ///
    /// ZIP 248 requires the decoding of a recognized payload to reject missing,
    /// truncated, or trailing bytes.
    pub fn decode<T>(&self, decode: impl FnOnce(&mut &[u8]) -> io::Result<T>) -> io::Result<T> {
        let mut payload = &self.data[..];
        let value = decode(&mut payload)?;
        if payload.is_empty() {
            Ok(value)
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "trailing bytes in v7 bundle payload",
            ))
        }
    }

    fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        Ok(Self {
            bundle: read_bundle_id(&mut reader)?,
            data: Vector::read_bytes(&mut reader)?,
        })
    }

    fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        write_bundle_id(&mut writer, self.bundle)?;
        CompactSize::write(&mut writer, self.data.len())?;
        writer.write_all(&self.data)
    }
}

/// Which map of a v7 transaction an entry belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapKind {
    /// `mValuePoolDeltas`.
    ValuePoolDeltas,
    /// `mEffectBundles`.
    EffectBundles,
    /// `mAuthBundles`.
    AuthBundles,
}

/// A violation of the ZIP 248 parsing rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum EnvelopeError {
    /// The `header` or `nVersionGroupId` field does not identify a v7 transaction.
    NotV7,
    /// `nConsensusBranchId` is zero.
    ZeroConsensusBranchId,
    /// A map has an entry whose bundle type is not greater than the previous entry's.
    UnorderedMap {
        /// The map with the out-of-order entry.
        map: MapKind,
        /// The bundle type of the out-of-order entry.
        bundle_type: BundleType,
    },
    /// A value pool delta entry has a zero value, which must be elided instead.
    ZeroValuePoolDelta(BundleType),
    /// Entries for one bundle type use different variants in different maps.
    InconsistentVariant(BundleType),
    /// An authorizing bundle has no effecting bundle of the same type.
    AuthWithoutEffect(BundleType),
    /// A bundle type or variant is larger than the largest `compactSize` value.
    IdOutOfRange(BundleId),
    /// A bundle payload is longer than the largest `compactSize` value.
    PayloadTooLong(BundleId),
}

impl fmt::Display for EnvelopeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotV7 => write!(f, "not a v7 transaction"),
            Self::ZeroConsensusBranchId => write!(f, "the consensus branch ID is zero"),
            Self::UnorderedMap { map, bundle_type } => write!(
                f,
                "{map:?} entry for bundle type {bundle_type} is not in strictly increasing order"
            ),
            Self::ZeroValuePoolDelta(t) => write!(f, "zero value pool delta for bundle type {t}"),
            Self::InconsistentVariant(t) => {
                write!(f, "bundle type {t} uses different variants across maps")
            }
            Self::AuthWithoutEffect(t) => {
                write!(f, "authorizing bundle type {t} has no effecting bundle")
            }
            Self::IdOutOfRange(id) => write!(f, "bundle identifier {id} is out of range"),
            Self::PayloadTooLong(id) => write!(f, "the payload of bundle {id} is too long"),
        }
    }
}

impl core::error::Error for EnvelopeError {}

/// A well-formed v7 transaction, with every bundle payload kept opaque.
///
/// The three maps are stored in encoding order, which the parsing rules make strictly
/// increasing by bundle type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Envelope {
    header: Header,
    value_pool_deltas: Vec<ValuePoolDelta>,
    effect_bundles: Vec<BundleData>,
    auth_bundles: Vec<BundleData>,
}

impl Envelope {
    /// Constructs an envelope, checking the ZIP 248 parsing rules and that the consensus
    /// branch ID is nonzero.
    pub fn new(
        header: Header,
        value_pool_deltas: Vec<ValuePoolDelta>,
        effect_bundles: Vec<BundleData>,
        auth_bundles: Vec<BundleData>,
    ) -> Result<Self, EnvelopeError> {
        if header.consensus_branch_id == 0 {
            return Err(EnvelopeError::ZeroConsensusBranchId);
        }
        check_parsing_rules(&value_pool_deltas, &effect_bundles, &auth_bundles)?;
        Ok(Self {
            header,
            value_pool_deltas,
            effect_bundles,
            auth_bundles,
        })
    }

    /// Returns the common transaction fields.
    pub fn header(&self) -> &Header {
        &self.header
    }

    /// Returns the entries of `mValuePoolDeltas`, in encoding order.
    pub fn value_pool_deltas(&self) -> &[ValuePoolDelta] {
        &self.value_pool_deltas
    }

    /// Returns the entries of `mEffectBundles`, in encoding order.
    pub fn effect_bundles(&self) -> &[BundleData] {
        &self.effect_bundles
    }

    /// Returns the entries of `mAuthBundles`, in encoding order.
    pub fn auth_bundles(&self) -> &[BundleData] {
        &self.auth_bundles
    }

    /// Returns `mValuePoolDeltas[bundle_type]`, which is zero for an absent entry.
    pub fn value_pool_delta(&self, bundle_type: BundleType) -> i64 {
        self.value_pool_deltas
            .binary_search_by_key(&bundle_type, |d| d.bundle.bundle_type)
            .map_or(0, |i| self.value_pool_deltas[i].value.get())
    }

    /// Returns the effecting payload of `bundle_type`, if present.
    pub fn effect_bundle(&self, bundle_type: BundleType) -> Option<&BundleData> {
        find_bundle(&self.effect_bundles, bundle_type)
    }

    /// Returns the authorizing payload of `bundle_type`, if present.
    pub fn auth_bundle(&self, bundle_type: BundleType) -> Option<&BundleData> {
        find_bundle(&self.auth_bundles, bundle_type)
    }

    /// Returns `true` if this is a coinbase transaction.
    ///
    /// A v7 transaction is a coinbase transaction if and only if `mEffectBundles` has an
    /// entry for the coinbase bundle type, whatever its variant.
    pub fn is_coinbase(&self) -> bool {
        self.effect_bundle(BundleType::COINBASE).is_some()
    }

    /// Decomposes the envelope into its header and maps.
    pub fn into_parts(
        self,
    ) -> (
        Header,
        Vec<ValuePoolDelta>,
        Vec<BundleData>,
        Vec<BundleData>,
    ) {
        (
            self.header,
            self.value_pool_deltas,
            self.effect_bundles,
            self.auth_bundles,
        )
    }

    /// Reads a v7 transaction, including its `header` and `nVersionGroupId` fields.
    ///
    /// The maps are validated once they have been read. Memory use grows only with the
    /// bytes actually read, but this reader imposes no size limit of its own, so callers
    /// reading untrusted input should bound its length (for example, to the block size).
    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        if reader.read_u32_le()? != V7_HEADER || reader.read_u32_le()? != V7_VERSION_GROUP_ID {
            return Err(invalid(EnvelopeError::NotV7));
        }
        Self::read_after_version(reader)
    }

    /// Reads a v7 transaction whose `header` and `nVersionGroupId` fields have already
    /// been read and checked.
    pub(crate) fn read_after_version<R: Read>(mut reader: R) -> io::Result<Self> {
        let header = Header::read_after_version(&mut reader)?;
        let value_pool_deltas = Vector::read(&mut reader, |r| ValuePoolDelta::read(r))?;
        let effect_bundles = Vector::read(&mut reader, |r| BundleData::read(r))?;
        let auth_bundles = Vector::read(&mut reader, |r| BundleData::read(r))?;
        Self::new(header, value_pool_deltas, effect_bundles, auth_bundles).map_err(invalid)
    }

    /// Writes the v7 encoding of this transaction.
    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        self.header.write(&mut writer)?;
        Vector::write(&mut writer, &self.value_pool_deltas, |w, d| d.write(w))?;
        Vector::write(&mut writer, &self.effect_bundles, |w, b| b.write(w))?;
        Vector::write(&mut writer, &self.auth_bundles, |w, b| b.write(w))
    }
}

/// Finds the entry for `bundle_type` in a map, which the parsing rules keep sorted.
fn find_bundle(map: &[BundleData], bundle_type: BundleType) -> Option<&BundleData> {
    map.binary_search_by_key(&bundle_type, |b| b.bundle.bundle_type)
        .ok()
        .map(|i| &map[i])
}

fn check_parsing_rules(
    value_pool_deltas: &[ValuePoolDelta],
    effect_bundles: &[BundleData],
    auth_bundles: &[BundleData],
) -> Result<(), EnvelopeError> {
    let maps = [
        (
            MapKind::ValuePoolDeltas,
            value_pool_deltas
                .iter()
                .map(|d| d.bundle)
                .collect::<Vec<_>>(),
        ),
        (
            MapKind::EffectBundles,
            effect_bundles.iter().map(|b| b.bundle).collect(),
        ),
        (
            MapKind::AuthBundles,
            auth_bundles.iter().map(|b| b.bundle).collect(),
        ),
    ];

    // Every identifier can be read back as a `compactSize`.
    let max = BundleType::new(MAX_COMPACT_SIZE);
    if let Some(id) = maps
        .iter()
        .flat_map(|(_, ids)| ids)
        .find(|id| id.bundle_type > max || id.variant > BundleVariant::new(MAX_COMPACT_SIZE))
    {
        return Err(EnvelopeError::IdOutOfRange(*id));
    }

    if let Some(bundle) = effect_bundles
        .iter()
        .chain(auth_bundles)
        .find(|b| b.data.len() > compact(MAX_COMPACT_SIZE))
    {
        return Err(EnvelopeError::PayloadTooLong(bundle.bundle));
    }

    // Each map has at most one entry per bundle type, in strictly increasing order.
    for (map, ids) in &maps {
        for pair in ids.windows(2) {
            if pair[1].bundle_type <= pair[0].bundle_type {
                return Err(EnvelopeError::UnorderedMap {
                    map: *map,
                    bundle_type: pair[1].bundle_type,
                });
            }
        }
    }

    // All entries for one bundle type use the same variant.
    let mut variants = BTreeMap::<BundleType, BundleVariant>::new();
    for id in maps.iter().flat_map(|(_, ids)| ids) {
        match variants.insert(id.bundle_type, id.variant) {
            Some(variant) if variant != id.variant => {
                return Err(EnvelopeError::InconsistentVariant(id.bundle_type));
            }
            _ => {}
        }
    }

    // Authorizing data cannot exist without effecting data of the same bundle. With the
    // variant check above, a matching type implies a matching variant. The maps are
    // sorted by now, so each lookup is a binary search.
    for auth in auth_bundles {
        if find_bundle(effect_bundles, auth.bundle.bundle_type).is_none() {
            return Err(EnvelopeError::AuthWithoutEffect(auth.bundle.bundle_type));
        }
    }

    Ok(())
}

fn read_bundle_id<R: Read>(mut reader: R) -> io::Result<BundleId> {
    Ok(BundleId::new(
        BundleType::new(CompactSize::read_t(&mut reader)?),
        BundleVariant::new(CompactSize::read_t(&mut reader)?),
    ))
}

/// Writes the `compactSize` encodings of a bundle type and variant.
pub(crate) fn write_bundle_id<W: Write>(mut writer: W, id: BundleId) -> io::Result<()> {
    CompactSize::write(&mut writer, compact(id.bundle_type.id()))?;
    CompactSize::write(&mut writer, compact(id.variant.id()))
}

fn compact(id: u32) -> usize {
    usize::try_from(id).expect("bundle identifiers are u32 values, which fit in usize")
}

fn invalid(error: EnvelopeError) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, error)
}
