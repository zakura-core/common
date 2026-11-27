//! The digests that the signatures of a bundle sign.

/// The digests that the signatures of a bundle sign.
///
/// In v5 and v6 transactions every signature of a bundle signs one transaction-wide
/// digest, which a `[u8; 32]` provides. In a v7 transaction ([ZIP 248]) each signature
/// signs a digest that commits to its position in the bundle.
///
/// Verifiers treat a missing digest as an invalid bundle. Builders require a digest for
/// every action of the bundle they sign.
///
/// [ZIP 248]: https://zips.z.cash/zip-0248
pub trait SignatureDigests {
    /// Returns the digest that the spend authorization signature of the action at
    /// `index` signs, or `None` if these digests describe no such action.
    fn spend_auth(&self, index: usize) -> Option<[u8; 32]>;

    /// Returns the digest that the binding signature signs.
    fn binding(&self) -> [u8; 32];
}

impl SignatureDigests for [u8; 32] {
    fn spend_auth(&self, _index: usize) -> Option<[u8; 32]> {
        Some(*self)
    }

    fn binding(&self) -> [u8; 32] {
        *self
    }
}

impl<T: SignatureDigests + ?Sized> SignatureDigests for &T {
    fn spend_auth(&self, index: usize) -> Option<[u8; 32]> {
        (**self).spend_auth(index)
    }

    fn binding(&self) -> [u8; 32] {
        (**self).binding()
    }
}
