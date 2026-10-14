//! Test stand-in for the infallible `OsRng` that `rand_core` 0.6 exposed.

/// The infallible OS RNG interface that `rand_core` 0.6 exposed as `OsRng`.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct OsRng;

impl rand::TryRng for OsRng {
    type Error = rand::rand_core::Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        rand::rand_core::UnwrapErr(rand::rngs::SysRng).try_next_u32()
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        rand::rand_core::UnwrapErr(rand::rngs::SysRng).try_next_u64()
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
        rand::rand_core::UnwrapErr(rand::rngs::SysRng).try_fill_bytes(dest)
    }
}

impl rand::TryCryptoRng for OsRng {}
