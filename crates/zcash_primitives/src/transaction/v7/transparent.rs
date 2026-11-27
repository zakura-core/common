//! The ZIP 248 transparent bundle encoding.

use alloc::vec::Vec;
use corez::io::{self, Read, Write};

use blake2b_simd::Hash as Blake2bHash;

use ::transparent::{
    address::Script,
    bundle::{self as transparent, OutPoint, TxIn, TxOut},
};
use zcash_protocol::encoding::{Array, CompactSize, Vector};

use super::sighash_info::{self, SighashInfo};
use crate::{
    encoding::{ReadBytesExt, WriteBytesExt},
    transaction::txid,
};

/// Returns `true` if a transparent bundle has effects, and so an entry in
/// `mEffectBundles`.
///
/// A v7 transparent bundle with neither inputs nor outputs is encoded by omitting it.
pub(crate) fn has_effects<A: transparent::Authorization>(bundle: &transparent::Bundle<A>) -> bool {
    !(bundle.vin.is_empty() && bundle.vout.is_empty())
}

/// Returns `true` if a transparent bundle has authorizing data, and so an entry in
/// `mAuthBundles`: exactly when it spends at least one input.
pub(crate) fn has_auth<A: transparent::Authorization>(bundle: &transparent::Bundle<A>) -> bool {
    !bundle.vin.is_empty()
}

/// The effecting data of a v7 transparent bundle: each input's previous output and
/// sequence number, and the outputs.
pub(crate) struct Effects {
    inputs: Vec<TxIn<transparent::EffectsOnly>>,
    outputs: Vec<TxOut>,
}

impl Effects {
    /// Reads the effecting data, which must have at least one input or output.
    pub(crate) fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let inputs = Vector::read(&mut reader, |r| {
            let prevout = OutPoint::read(&mut *r)?;
            Ok(TxIn::from_parts(prevout, (), r.read_u32_le()?))
        })?;
        let outputs = Vector::read(&mut reader, TxOut::read)?;
        if inputs.is_empty() && outputs.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "an empty v7 transparent bundle must be omitted",
            ));
        }
        Ok(Self { inputs, outputs })
    }

    /// Returns `true` if the bundle spends at least one input, and so has authorizing
    /// data.
    pub(crate) fn has_inputs(&self) -> bool {
        !self.inputs.is_empty()
    }

    /// T.3.0 `transparent_effects_digest`.
    pub(crate) fn effects_digest(&self) -> Blake2bHash {
        txid::hash_transparent_txid_data(Some(&txid::transparent_digests(
            &self.inputs,
            &self.outputs,
        )))
    }

    /// Reads the authorizing data: one `scriptSig` per input, each with a `sighashInfo`
    /// of any variant.
    pub(crate) fn read_auth<R: Read>(&self, mut reader: R) -> io::Result<Vec<InputAuth>> {
        Array::read(&mut reader, self.inputs.len(), |r| {
            Ok(InputAuth {
                sighash_info: SighashInfo::read(&mut *r)?,
                script_sig: Script::read(r)?,
            })
        })
    }

    /// Assembles the bundle from these effects and the authorizing data of each input,
    /// which must use sighash variant 0.
    pub(crate) fn into_bundle(
        self,
        auth: Vec<InputAuth>,
    ) -> io::Result<transparent::Bundle<transparent::Authorized>> {
        assert_eq!(
            self.inputs.len(),
            auth.len(),
            "the authorizing data was read with one scriptSig per input"
        );
        let vin = self
            .inputs
            .into_iter()
            .zip(auth)
            .map(|(input, auth)| {
                auth.sighash_info.require_v0()?;
                Ok(TxIn::from_parts(
                    input.prevout().clone(),
                    auth.script_sig,
                    input.sequence(),
                ))
            })
            .collect::<io::Result<_>>()?;
        Ok(transparent::Bundle {
            vin,
            vout: self.outputs,
            authorization: transparent::Authorized,
        })
    }
}

/// The authorizing data of one v7 transparent input: `TransparentInputAuth`.
pub(crate) struct InputAuth {
    sighash_info: SighashInfo,
    script_sig: Script,
}

/// A.1.0 `transparent_auth_digest`, over the authorizing data of each input.
pub(crate) fn auth_digest(auth: &[InputAuth]) -> Blake2bHash {
    txid::transparent_v7_auth_digest(
        auth.iter()
            .map(|input| (input.sighash_info.field_encoding(), &input.script_sig)),
    )
}

/// Writes the effecting data of a v7 transparent bundle.
pub(crate) fn write_effects<W: Write, A: transparent::Authorization>(
    mut writer: W,
    bundle: &transparent::Bundle<A>,
) -> io::Result<()> {
    CompactSize::write(&mut writer, bundle.vin.len())?;
    for txin in &bundle.vin {
        txin.prevout().write(&mut writer)?;
        writer.write_u32_le(txin.sequence())?;
    }
    Vector::write(&mut writer, &bundle.vout, |w, out| out.write(w))
}

/// Writes the authorizing data of a v7 transparent bundle.
pub(crate) fn write_auth<W: Write>(
    mut writer: W,
    bundle: &transparent::Bundle<transparent::Authorized>,
) -> io::Result<()> {
    for txin in &bundle.vin {
        sighash_info::write_v0(&mut writer)?;
        txin.script_sig().write(&mut writer)?;
    }
    Ok(())
}
