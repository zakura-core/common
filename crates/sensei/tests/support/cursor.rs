//! Bounds-checked byte readers and public field/point decoding.

use zakura_sensei::{Error, Fp, Fr, NonIdentityPallasPoint, PallasPoint, SpendValidatingKey};

pub const FIELD_SIZE: usize = 32;

pub struct Cursor<'a> {
    input: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    pub fn new(input: &'a [u8]) -> Self {
        Self { input, offset: 0 }
    }

    pub fn take<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        Ok(self
            .take_slice(N)?
            .try_into()
            .expect("slice length is fixed"))
    }

    pub fn take_slice(&mut self, length: usize) -> Result<&'a [u8], Error> {
        let end = self.offset.checked_add(length).ok_or(Error::InvalidInput)?;
        let bytes = self
            .input
            .get(self.offset..end)
            .ok_or(Error::InvalidInput)?;
        self.offset = end;
        Ok(bytes)
    }

    pub fn read_u16(&mut self) -> Result<u16, Error> {
        Ok(u16::from_le_bytes(self.take()?))
    }

    pub fn read_u32(&mut self) -> Result<u32, Error> {
        Ok(u32::from_le_bytes(self.take()?))
    }

    pub fn read_u64(&mut self) -> Result<u64, Error> {
        Ok(u64::from_le_bytes(self.take()?))
    }

    pub fn read_fp(&mut self) -> Result<Fp, Error> {
        Fp::from_bytes(self.take()?)
    }

    pub fn read_fr(&mut self) -> Result<Fr, Error> {
        Fr::from_bytes(self.take()?)
    }

    pub fn read_point(&mut self) -> Result<PallasPoint, Error> {
        PallasPoint::from_bytes(self.take()?)
    }

    pub fn read_nonidentity_point(&mut self) -> Result<NonIdentityPallasPoint, Error> {
        NonIdentityPallasPoint::from_bytes(self.take()?)
    }

    pub fn read_spend_validating_key(&mut self) -> Result<SpendValidatingKey, Error> {
        SpendValidatingKey::from_bytes(self.take()?)
    }

    pub fn read_bool(&mut self) -> Result<bool, Error> {
        let bytes = self.take::<FIELD_SIZE>()?;
        if bytes == [0; FIELD_SIZE] {
            Ok(false)
        } else if bytes[0] == 1 && bytes[1..].iter().all(|byte| *byte == 0) {
            Ok(true)
        } else {
            Err(Error::InvalidInput)
        }
    }

    pub fn is_finished(&self) -> bool {
        self.offset == self.input.len()
    }
}
