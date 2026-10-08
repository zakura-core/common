use core::convert::Infallible;

/// Adapts the `rand_core 0.6` API used by FROST to the `rand_core 0.10` API
/// required by `ff 0.14` field implementations.
pub(super) struct RngCompat<'a, R>(&'a mut R);

impl<'a, R> RngCompat<'a, R> {
    pub(super) fn new(rng: &'a mut R) -> Self {
        Self(rng)
    }
}

impl<R: rand_core_06::RngCore> rand_core::TryRng for RngCompat<'_, R> {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        Ok(self.0.next_u32())
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        Ok(self.0.next_u64())
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
        self.0.fill_bytes(dest);
        Ok(())
    }
}

impl<R: rand_core_06::RngCore + rand_core_06::CryptoRng> rand_core::TryCryptoRng
    for RngCompat<'_, R>
{
}
