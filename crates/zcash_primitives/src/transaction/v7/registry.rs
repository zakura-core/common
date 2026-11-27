//! Bundle identifiers and the v7 bundle type registry.

use core::fmt;

/// A ZIP 248 `bundleType`: the protocol or value pool that a bundle operates on.
///
/// Encoded as a `compactSize`, so every value fits in a `u32`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BundleType(u32);

impl BundleType {
    /// The transparent bundle.
    pub const TRANSPARENT: Self = Self(0);
    /// The coinbase bundle.
    pub const COINBASE: Self = Self(1);
    /// The Sapling bundle.
    pub const SAPLING: Self = Self(2);
    /// The Orchard bundle, acting on the Orchard pool.
    pub const ORCHARD: Self = Self(3);
    /// The Ironwood bundle, acting on the Ironwood pool.
    pub const IRONWOOD: Self = Self(4);
    /// The transaction fee bundle of ZIP 2002.
    pub const FEE: Self = Self(5);
    /// The NSM field of ZIP 233.
    pub const NSM: Self = Self(6);

    /// Constructs a bundle type from its identifier.
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns the identifier of this bundle type.
    pub const fn id(self) -> u32 {
        self.0
    }
}

impl fmt::Display for BundleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// A ZIP 248 `bundleVariant`: a variant of the protocol identified by a [`BundleType`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BundleVariant(u32);

impl BundleVariant {
    /// Variant 0, the only variant registered for each bundle type in v7.
    pub const V0: Self = Self(0);

    /// Constructs a bundle variant from its identifier.
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns the identifier of this bundle variant.
    pub const fn id(self) -> u32 {
        self.0
    }
}

/// A `(bundleType, bundleVariant)` pair identifying one kind of bundle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BundleId {
    /// The bundle type.
    pub bundle_type: BundleType,
    /// The variant of the bundle type.
    pub variant: BundleVariant,
}

impl BundleId {
    /// Transparent, variant 0.
    pub const TRANSPARENT: Self = Self::v0(BundleType::TRANSPARENT);
    /// Coinbase, variant 0.
    pub const COINBASE: Self = Self::v0(BundleType::COINBASE);
    /// Sapling, variant 0.
    pub const SAPLING: Self = Self::v0(BundleType::SAPLING);
    /// Orchard, variant 0.
    pub const ORCHARD: Self = Self::v0(BundleType::ORCHARD);
    /// Ironwood, variant 0.
    pub const IRONWOOD: Self = Self::v0(BundleType::IRONWOOD);
    /// Transaction fee, variant 0.
    pub const FEE: Self = Self::v0(BundleType::FEE);
    /// ZIP 233 NSM field, variant 0.
    pub const NSM: Self = Self::v0(BundleType::NSM);

    /// Constructs a bundle identifier.
    pub const fn new(bundle_type: BundleType, variant: BundleVariant) -> Self {
        Self {
            bundle_type,
            variant,
        }
    }

    const fn v0(bundle_type: BundleType) -> Self {
        Self::new(bundle_type, BundleVariant::V0)
    }

    /// Returns which maps of a v7 transaction may contain an entry for this pair, or
    /// `None` if the pair is not registered for v7.
    ///
    /// Registration alone does not activate a pair: full validators separately check
    /// that it is active in the consensus epoch of the block.
    pub fn registration(self) -> Option<Registration> {
        const ALL: Registration = Registration {
            value_pool_delta: true,
            effecting: true,
            authorizing: true,
        };
        const DELTA_ONLY: Registration = Registration {
            value_pool_delta: true,
            effecting: false,
            authorizing: false,
        };
        match self {
            Self::TRANSPARENT | Self::SAPLING | Self::ORCHARD | Self::IRONWOOD => Some(ALL),
            Self::COINBASE => Some(Registration {
                authorizing: false,
                ..ALL
            }),
            Self::FEE | Self::NSM => Some(DELTA_ONLY),
            _ => None,
        }
    }
}

impl fmt::Display for BundleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.bundle_type.0, self.variant.0)
    }
}

/// The maps of a v7 transaction in which a registered bundle may have an entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Registration {
    /// Whether the bundle may have an entry in `mValuePoolDeltas`.
    pub value_pool_delta: bool,
    /// Whether the bundle may have an entry in `mEffectBundles`.
    pub effecting: bool,
    /// Whether the bundle may have an entry in `mAuthBundles`.
    pub authorizing: bool,
}

#[cfg(test)]
mod tests {
    use super::{BundleId, BundleType, BundleVariant};

    #[test]
    fn registry_matches_zip_248() {
        // (type, delta, effect, auth), from the v7 Transaction Bundle Type Registry.
        let expected = [
            (0, true, true, true),
            (1, true, true, false),
            (2, true, true, true),
            (3, true, true, true),
            (4, true, true, true),
            (5, true, false, false),
            (6, true, false, false),
        ];
        for (id, delta, effect, auth) in expected {
            let reg = BundleId::new(BundleType::new(id), BundleVariant::V0)
                .registration()
                .expect("registered");
            assert_eq!(
                (reg.value_pool_delta, reg.effecting, reg.authorizing),
                (delta, effect, auth),
                "bundle type {id}"
            );
        }
        assert_eq!(
            BundleId::new(BundleType::new(7), BundleVariant::V0).registration(),
            None
        );
        assert_eq!(
            BundleId::new(BundleType::SAPLING, BundleVariant::new(1)).registration(),
            None
        );
    }
}
