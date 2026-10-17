use super::*;
use crate::backend::pasta_curves::glv::{Decomposed, Table};
#[allow(unused_imports)]
use crate::backend::prelude::*;
use alloc::boxed::Box;
/// What a prepared ephemeral key carries.
///
/// Individually-prepared keys carry a `group::Wnaf` window table, consumed by
/// the per-item multiplication. Batch-prepared keys carry a GLV odd-multiples
/// window instead (see `pasta_curves::glv`), which is cheaper to build across a
/// batch (one shared normalization) and cheaper to multiply against (a
/// shared-doubling ladder over the endomorphism split). Both produce
/// identical shared secrets.
#[derive(Clone, Debug)]
enum PreparedEpkInner {
    /// A `group::Wnaf` window table.
    Wnaf(PreparedNonIdentityBase),
    /// A GLV Eisenstein digit-orbit window, boxed to keep the enum small
    /// (1 KiB on the heap: eight orbit points with the x-coordinates stored
    /// in all three endomorphism rotations).
    Tabled(Box<Table<pallas::Point>>),
}

/// An Orchard ephemeral public key that has been precomputed for trial decryption.
#[derive(Clone, Debug)]
pub struct PreparedEphemeralPublicKey(PreparedEpkInner);

impl PreparedEphemeralPublicKey {
    pub(crate) fn new(epk: EphemeralPublicKey) -> Self {
        PreparedEphemeralPublicKey(PreparedEpkInner::Wnaf(PreparedNonIdentityBase::new(epk.0)))
    }

    /// Prepares every ephemeral key in a batch by building its GLV window,
    /// sharing one batch normalization (a single field inversion) across the
    /// whole set, where individual preparation pays one inversion per key.
    /// `None` lanes (ephemeral keys that failed to decode) pass through as
    /// `None`.
    pub(crate) fn batch_tabled(
        epks: Vec<Option<EphemeralPublicKey>>,
    ) -> Vec<Option<PreparedEphemeralPublicKey>> {
        let live: Vec<pallas::Point> = epks
            .iter()
            .filter_map(|e| e.as_ref().map(|e| *e.0))
            .collect();
        let mut tables = Table::<pallas::Point>::batch(&live).into_iter();
        epks.into_iter()
            .map(|e| {
                e.map(|_| {
                    PreparedEphemeralPublicKey(PreparedEpkInner::Tabled(Box::new(
                        tables.next().expect("one table per live epk"),
                    )))
                })
            })
            .collect()
    }

    pub(crate) fn agree(&self, ivk: &PreparedIncomingViewingKey) -> SharedSecret {
        match &self.0 {
            PreparedEpkInner::Wnaf(base) => SharedSecret(ka_orchard_prepared(&ivk.0, base)),
            // The product of a non-zero scalar and a non-identity point in the
            // prime-order Pallas group is non-identity.
            PreparedEpkInner::Tabled(table) => SharedSecret(
                NonIdentityPallasPoint::expect_non_identity(table.mul(&ivk.raw_scalar())),
            ),
        }
    }

    /// The GLV window table, if this key was batch-prepared.
    fn table(&self) -> Option<&Table<pallas::Point>> {
        match &self.0 {
            PreparedEpkInner::Wnaf(_) => None,
            PreparedEpkInner::Tabled(table) => Some(table),
        }
    }

    /// Key agreement between one viewing key — with its GLV decomposition
    /// precomputed, hoisting the digit recoding out of the per-output loop —
    /// and a whole batch of prepared ephemeral keys.
    ///
    /// All GLV-tabled keys in the batch are multiplied by one synchronized
    /// ladder ([`Table::mul_decomposed_batch`]): the batch shares the
    /// viewing key's column schedule, so for large batches every ladder
    /// column's field inversions are batched across the whole set (and
    /// smaller batches run the same per-point ladders as before).
    /// Individually-prepared (wNAF) keys fall back to the per-item
    /// multiplication; `None` lanes (undecodable ephemeral keys) pass
    /// through as `None`.
    pub(crate) fn batch_agree(
        ivk: &PreparedIncomingViewingKey,
        epks: &[Option<&PreparedEphemeralPublicKey>],
    ) -> Vec<Option<SharedSecret>> {
        let decomposed = Decomposed::<pallas::Point>::new(&ivk.raw_scalar());
        let tables: Vec<&Table<pallas::Point>> = epks
            .iter()
            .filter_map(|epk| epk.and_then(|epk| epk.table()))
            .collect();
        let mut products = Table::mul_decomposed_batch(&tables, &decomposed).into_iter();
        epks.iter()
            .map(|epk| {
                epk.map(|epk| match &epk.0 {
                    PreparedEpkInner::Wnaf(base) => SharedSecret(ka_orchard_prepared(&ivk.0, base)),
                    // The product of a non-zero scalar and a non-identity
                    // point in the prime-order Pallas group is non-identity.
                    PreparedEpkInner::Tabled(_) => {
                        SharedSecret(NonIdentityPallasPoint::expect_non_identity(
                            products.next().expect("one product per tabled epk"),
                        ))
                    }
                })
            })
            .collect()
    }
}
