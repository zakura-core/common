//! Independent unit IWPR decoding and frozen RNG tape replay.

use crate::{
    Action, Error, Fp, Fq, NonIdentityPallasPoint, PallasPoint, PrivateWitness, ProvingRequest,
    PublicStatement, SpendValidatingKey,
};

/// Replays a fixture RNG tape and fails on exhaustion; the frozen word count
/// is checked by callers through [`TapeRng::words_consumed`].
pub(crate) struct TapeRng {
    tape: &'static [u8],
    cursor: usize,
}

impl TapeRng {
    pub(crate) fn new(tape: &'static [u8]) -> Self {
        Self { tape, cursor: 0 }
    }

    pub(crate) fn words_consumed(&self) -> usize {
        self.cursor
    }
}

impl crate::RandomSource for TapeRng {
    fn next_u64(&mut self) -> Result<u64, crate::RandomnessError> {
        let word = self
            .tape
            .get(self.cursor * 8..(self.cursor + 1) * 8)
            .ok_or(crate::RandomnessError)?;
        self.cursor += 1;
        Ok(u64::from_le_bytes(word.try_into().unwrap()))
    }
}

/// Request format selected by `IWPR/1`.
const REQUEST_FORMAT_VERSION: u16 = 1;

/// Target selector version carried by the internal `IWPR/1` fixture codec.
const TARGET_FORMAT_VERSION: u16 = 1;

/// Frozen identifier for the pinned proving target.
const TARGET_ID: [u8; 32] = [
    0xec, 0x64, 0xc2, 0xd4, 0x91, 0xf2, 0xbe, 0x42, 0x25, 0x4c, 0xac, 0xd2, 0xa5, 0x33, 0xd6, 0xe7,
    0x29, 0x05, 0x41, 0xaa, 0x6f, 0xbb, 0x78, 0xf9, 0xb3, 0xe2, 0x5c, 0xa9, 0x2c, 0x39, 0xfb, 0x77,
];

const MAGIC: [u8; 4] = *b"IWPR";
const FIELD_SIZE: usize = 32;
const PUBLIC_STATEMENT_SIZE: usize = 10 * FIELD_SIZE;
const PRIVATE_WITNESS_SIZE: usize = 1_524;
pub(crate) const ACTION_SIZE: usize = PUBLIC_STATEMENT_SIZE + PRIVATE_WITNESS_SIZE;
pub(crate) const HEADER_SIZE: usize = 44;

pub(crate) fn decode_iwpr(input: &[u8]) -> Result<ProvingRequest, Error> {
    let mut cursor = Cursor::new(input);
    if cursor.take::<4>()? != MAGIC
        || cursor.read_u16()? != REQUEST_FORMAT_VERSION
        || cursor.read_u16()? != TARGET_FORMAT_VERSION
        || cursor.take::<32>()? != TARGET_ID
    {
        return Err(Error::InvalidInput);
    }

    let action_count = usize::try_from(cursor.read_u32()?).map_err(|_| Error::InvalidInput)?;
    let expected_size = action_count
        .checked_mul(ACTION_SIZE)
        .and_then(|actions| HEADER_SIZE.checked_add(actions))
        .ok_or(Error::InvalidInput)?;
    if input.len() != expected_size {
        return Err(Error::InvalidInput);
    }

    let actions = (0..action_count)
        .map(|_| decode_action(&mut cursor))
        .collect::<Result<Vec<_>, _>>()?;
    if !cursor.is_finished() {
        return Err(Error::InvalidInput);
    }
    ProvingRequest::new(actions)
}

fn decode_action(cursor: &mut Cursor<'_>) -> Result<Action, Error> {
    let statement = PublicStatement {
        anchor: cursor.read_fp()?,
        cv_net: (cursor.read_fp()?, cursor.read_fp()?),
        nf_old: cursor.read_fp()?,
        rk: (cursor.read_fp()?, cursor.read_fp()?),
        cmx: cursor.read_fp()?,
        enable_spend: cursor.read_bool()?,
        enable_output: cursor.read_bool()?,
        disable_cross_address: cursor.read_bool()?,
    };

    let mut path = [Fp::ZERO; crate::types::MERKLE_DEPTH];
    for sibling in &mut path {
        *sibling = cursor.read_fp()?;
    }
    let witness = PrivateWitness {
        path,
        position: cursor.read_u32()?,
        g_d_old: cursor.read_nonidentity_point()?,
        pk_d_old: cursor.read_nonidentity_point()?,
        v_old: cursor.read_u64()?,
        rho_old: cursor.read_fp()?,
        psi_old: cursor.read_fp()?,
        rcm_old: cursor.read_fq()?,
        cm_old: cursor.read_point()?,
        alpha: cursor.read_fq()?,
        ak: cursor.read_spend_validating_key()?,
        nk: cursor.read_fp()?,
        rivk: cursor.read_fq()?,
        g_d_new: cursor.read_nonidentity_point()?,
        pk_d_new: cursor.read_nonidentity_point()?,
        v_new: cursor.read_u64()?,
        psi_new: cursor.read_fp()?,
        rcm_new: cursor.read_fq()?,
        rcv: cursor.read_fq()?,
    };
    Ok(Action { statement, witness })
}

struct Cursor<'a> {
    input: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self { input, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        let end = self.offset.checked_add(N).ok_or(Error::InvalidInput)?;
        let bytes = self
            .input
            .get(self.offset..end)
            .ok_or(Error::InvalidInput)?;
        self.offset = end;
        bytes.try_into().map_err(|_| Error::InvalidInput)
    }

    fn read_u16(&mut self) -> Result<u16, Error> {
        Ok(u16::from_le_bytes(self.take()?))
    }

    fn read_u32(&mut self) -> Result<u32, Error> {
        Ok(u32::from_le_bytes(self.take()?))
    }

    fn read_u64(&mut self) -> Result<u64, Error> {
        Ok(u64::from_le_bytes(self.take()?))
    }

    fn read_fp(&mut self) -> Result<Fp, Error> {
        Fp::from_bytes(self.take()?)
    }

    fn read_fq(&mut self) -> Result<Fq, Error> {
        Fq::from_bytes(self.take()?)
    }

    fn read_point(&mut self) -> Result<PallasPoint, Error> {
        PallasPoint::from_bytes(self.take()?)
    }

    fn read_nonidentity_point(&mut self) -> Result<NonIdentityPallasPoint, Error> {
        NonIdentityPallasPoint::from_bytes(self.take()?)
    }

    fn read_spend_validating_key(&mut self) -> Result<SpendValidatingKey, Error> {
        SpendValidatingKey::from_bytes(self.take()?)
    }

    fn read_bool(&mut self) -> Result<bool, Error> {
        let value = self.read_fp()?;
        if value.is_zero() {
            Ok(false)
        } else if value == Fp::ONE {
            Ok(true)
        } else {
            Err(Error::InvalidInput)
        }
    }

    fn is_finished(&self) -> bool {
        self.offset == self.input.len()
    }
}
