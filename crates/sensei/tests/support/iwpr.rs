//! Independent IWPR request decoding through Sensei's public constructors.

#[cfg(feature = "prover")]
use super::cursor::Cursor;
use super::cursor::FIELD_SIZE;
#[cfg(feature = "prover")]
use zakura_sensei::{Action, Error, Fp, PrivateWitness, ProvingRequest, PublicStatement};

pub const MAGIC: [u8; 4] = *b"IWPR";
pub const REQUEST_FORMAT_VERSION: u16 = 1;
pub const TARGET_FORMAT_VERSION: u16 = 1;
/// Frozen identifier for the pinned proving target.
pub const TARGET_ID: [u8; 32] = [
    0xec, 0x64, 0xc2, 0xd4, 0x91, 0xf2, 0xbe, 0x42, 0x25, 0x4c, 0xac, 0xd2, 0xa5, 0x33, 0xd6, 0xe7,
    0x29, 0x05, 0x41, 0xaa, 0x6f, 0xbb, 0x78, 0xf9, 0xb3, 0xe2, 0x5c, 0xa9, 0x2c, 0x39, 0xfb, 0x77,
];
pub const MERKLE_DEPTH: usize = 32;
pub const PUBLIC_STATEMENT_SIZE: usize = 10 * FIELD_SIZE;
pub const PRIVATE_WITNESS_SIZE: usize = 1_524;
pub const ACTION_SIZE: usize = PUBLIC_STATEMENT_SIZE + PRIVATE_WITNESS_SIZE;
pub const HEADER_SIZE: usize = 44;

#[cfg(feature = "prover")]
pub fn decode_actions(input: &[u8]) -> Result<Vec<Action>, Error> {
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
    Ok(actions)
}

#[cfg(feature = "prover")]
pub fn decode_request(input: &[u8]) -> Result<ProvingRequest, Error> {
    ProvingRequest::new(decode_actions(input)?)
}

#[cfg(feature = "prover")]
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

    let mut path = [Fp::from_bytes([0; FIELD_SIZE])?; MERKLE_DEPTH];
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
        rcm_old: cursor.read_fr()?,
        cm_old: cursor.read_point()?,
        alpha: cursor.read_fr()?,
        ak: cursor.read_spend_validating_key()?,
        nk: cursor.read_fp()?,
        rivk: cursor.read_fr()?,
        g_d_new: cursor.read_nonidentity_point()?,
        pk_d_new: cursor.read_nonidentity_point()?,
        v_new: cursor.read_u64()?,
        psi_new: cursor.read_fp()?,
        rcm_new: cursor.read_fr()?,
        rcv: cursor.read_fr()?,
    };
    Ok(Action { statement, witness })
}
