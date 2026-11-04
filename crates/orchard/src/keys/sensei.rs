use super::*;
#[allow(unused_imports)]
use crate::backend::prelude::*;
/// An Orchard ephemeral public key with all endomorphism rotations prepared.
#[derive(Clone, Debug)]
pub struct PreparedEphemeralPublicKey(PreparedNonIdentityBase);
impl PreparedEphemeralPublicKey {
    pub(crate) fn new(epk: EphemeralPublicKey) -> Self {
        Self(PreparedNonIdentityBase::new(epk.0))
    }
    /// Prepares live keys together. Large batches use affine addition chains;
    /// undecodable positions retain their original ordering as `None`.
    pub(crate) fn batch_tabled(epks: Vec<Option<EphemeralPublicKey>>) -> Vec<Option<Self>> {
        let live: Vec<_> = epks
            .iter()
            .filter_map(|epk| {
                epk.as_ref().map(|epk| {
                    sensei::NonIdentityPallasPoint::from_native(
                        *epk.0
                            .native()
                            .to_point()
                            .as_affine()
                            .expect("decoded nonidentity key"),
                    )
                })
            })
            .collect();
        let mut tables = sensei::primitives::agreement::PreparedBase::batch(&live).into_iter();
        epks.into_iter()
            .map(|epk| {
                epk.map(|_| {
                    Self(PreparedNonIdentityBase::from_prepared(
                        tables.next().expect("one table per live key"),
                    ))
                })
            })
            .collect()
    }
    pub(crate) fn agree(&self, ivk: &PreparedIncomingViewingKey) -> SharedSecret {
        SharedSecret(ka_orchard_prepared(&ivk.0, &self.0))
    }
    /// Borrows independently retained tables and reuses the IVK's digit schedule.
    /// The backend supplies synchronized affine ladders and shared inversions.
    pub(crate) fn batch_agree(
        ivk: &PreparedIncomingViewingKey,
        epks: &[Option<&Self>],
    ) -> Vec<Option<SharedSecret>> {
        let tables: Vec<_> = epks
            .iter()
            .filter_map(|epk| epk.map(|epk| epk.0.table()))
            .collect();
        let mut products =
            sensei::primitives::agreement::PreparedBase::multiply_batch(&tables, ivk.0.prepared())
                .into_iter();
        epks.iter()
            .map(|epk| {
                epk.map(|_| {
                    SharedSecret(NonIdentityPallasPoint::expect_non_identity(
                        products.next().expect("one product per live key"),
                    ))
                })
            })
            .collect()
    }
}
