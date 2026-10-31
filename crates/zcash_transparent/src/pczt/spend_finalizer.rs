use zcash_script::{pattern::push_script, pv, script, solver};

use crate::address::TransparentAddress;

impl super::Bundle {
    /// Finalizes the spends for this bundle.
    ///
    /// Returns an error if any spend uses an unsupported script format. The supported
    /// script formats are:
    /// - P2PKH
    /// - P2SH with one of these redeem script formats:
    ///   - P2MS
    pub fn finalize_spends(&mut self) -> Result<(), SpendFinalizerError> {
        // For each input, the Spend Finalizer determines if the input has enough data to
        // pass validation. If it does, it must construct the `script_sig` and place it
        // into the PCZT input. If `script_sig` is empty for an input, the field should
        // remain unset rather than assigned an empty array.
        for input in &mut self.inputs {
            TransparentAddress::from_script_from_chain(&input.script_pubkey)
                .ok_or(SpendFinalizerError::UnsupportedScriptPubkey)
                .and_then(|address| match address {
                    TransparentAddress::PublicKeyHash(hash) => {
                        let mut iter = input.partial_signatures.iter();
                        match (iter.next(), iter.next()) {
                            (Some(entry), None) => Ok(entry),
                            (None, _) => Err(SpendFinalizerError::MissingSignature),
                            (Some(_), Some(_)) => Err(SpendFinalizerError::UnexpectedSignatures),
                        }
                        .and_then(|(pubkey, sig_bytes)| {
                            // Check that the signature is for this input.
                            if hash[..] != crate::util::hash160::hash(pubkey)[..] {
                                Err(SpendFinalizerError::UnexpectedSignatures)
                            } else {
                                // P2PKH scriptSig
                                input.script_sig = Some(script::Component(vec![
                                    pv::push_value(sig_bytes)
                                        .ok_or(SpendFinalizerError::InvalidSignature)?,
                                    // `pubkey` is a fixed 33-byte compressed key, so its push always fits.
                                    pv::push_value(pubkey).expect("33-byte pubkey fits"),
                                ]));
                                Ok(())
                            }
                        })
                    }
                    TransparentAddress::ScriptHash(_) => {
                        let redeem_script = input
                            .redeem_script
                            .as_ref()
                            .ok_or(SpendFinalizerError::MissingRedeemScript)?
                            .refine()
                            .map_err(|_| SpendFinalizerError::UnsupportedRedeemScript)?;

                        match solver::standard(&redeem_script) {
                            Some(solver::ScriptKind::MultiSig { required, pubkeys }) => {
                                // P2MS-in-P2SH `script_sig` format is:
                                // - Dummy OP_0 to bypass OP_CHECKMULTISIG bug.
                                let mut script_sig = vec![pv::_0];

                                // - PushData(signature) * required
                                //
                                // The OP_CHECKMULTISIG logic matches pubkeys and
                                // signatures together sequentially, so we look for
                                // signatures in the order that the pubkeys exist in
                                // `redeem_script`.
                                let mut signatures_found = 0;
                                let mut skipped_uncompressed = false;
                                for pubkey in pubkeys {
                                    // Once we reach the threshold of required signatures,
                                    // any additional signatures present in the PCZT are
                                    // discarded.
                                    if signatures_found == required {
                                        break;
                                    }

                                    // PCZT only carries signatures for compressed pubkeys,
                                    // so the other keys in the script can still meet the
                                    // threshold.
                                    let Ok(pubkey) = <[u8; 33]>::try_from(pubkey.as_slice()) else {
                                        skipped_uncompressed = true;
                                        continue;
                                    };

                                    // If we have a signature from this pubkey, use it.
                                    if let Some(sig) = input.partial_signatures.get(&pubkey) {
                                        // Valid signatures always fit into `PushData`s.
                                        script_sig.push(
                                            pv::push_value(sig)
                                                .ok_or(SpendFinalizerError::InvalidSignature)?,
                                        );
                                        signatures_found += 1;
                                    }
                                }
                                if signatures_found < required {
                                    return Err(if skipped_uncompressed {
                                        SpendFinalizerError::UncompressedPubkeyInScript
                                    } else {
                                        SpendFinalizerError::MissingSignature
                                    });
                                }

                                // - PushData(redeem_script)
                                script_sig.push(
                                    push_script(&redeem_script)
                                        .ok_or(SpendFinalizerError::RedeemScriptTooLong)?,
                                );

                                // P2SH scriptSig
                                input.script_sig = Some(script::Component(script_sig));

                                Ok(())
                            }
                            _ => Err(SpendFinalizerError::UnsupportedScriptPubkey),
                        }
                    }
                })?
        }

        // All other data except the UTXO and proprietary fields in the input should be
        // cleared from the PSBT. The UTXO should be kept to allow Transaction Extractors
        // to verify the final network serialized transaction.
        for input in &mut self.inputs {
            input.required_time_lock_time = None;
            input.required_height_lock_time = None;
            input.redeem_script = None;
            input.partial_signatures.clear();
            input.bip32_derivation.clear();
            input.ripemd160_preimages.clear();
            input.sha256_preimages.clear();
            input.hash160_preimages.clear();
            input.hash256_preimages.clear();
        }

        Ok(())
    }
}

/// Errors that can occur while finalizing the transparent inputs of a PCZT bundle.
#[derive(Debug)]
pub enum SpendFinalizerError {
    /// `script_pubkey` is a P2SH script, but `redeem_script` is not set.
    MissingRedeemScript,
    /// `script_pubkey` is a P2SH script, but `redeem_script` is too long for a `PushData`.
    RedeemScriptTooLong,
    /// `partial_signatures` contained too few signatures.
    MissingSignature,
    /// `partial_signatures` contained an invalid signature.
    InvalidSignature,
    /// `redeem_script` contained an uncompressed pubkey, which PCZT cannot carry a
    /// signature for, and the signatures for its compressed pubkeys did not meet the
    /// threshold.
    UncompressedPubkeyInScript,
    /// `partial_signatures` contained unexpected signatures.
    UnexpectedSignatures,
    /// The `script_pubkey` kind is unsupported.
    UnsupportedScriptPubkey,
    /// The `redeem_script` kind is unsupported.
    UnsupportedRedeemScript,
}

#[cfg(all(test, feature = "std", feature = "transparent-inputs"))]
mod tests {
    use secp256k1::SecretKey;
    use zcash_protocol::value::Zatoshis;
    use zcash_script::{
        interpreter::{CallbackTransactionSignatureChecker, Flags},
        pattern::check_multisig,
        script::{Component, Evaluable, FromChain, Raw},
    };

    use super::SpendFinalizerError;
    use crate::{
        address::TransparentAddress,
        builder::TransparentBuilder,
        bundle::{OutPoint, TxOut},
    };

    /// Finalizes a 2-of-3 multisig spend whose first key is uncompressed, signed by the
    /// keys at `signers` (indices into the three keys).
    fn finalize(signers: &[usize]) -> Result<bool, SpendFinalizerError> {
        let sks = [1u8, 2, 3].map(|i| SecretKey::from_secret_bytes([i; 32]).unwrap());
        let pk = |i: usize| secp256k1::PublicKey::from_secret_key(&sks[i]);
        let uncompressed = pk(0).serialize_uncompressed();
        let compressed = [pk(1).serialize(), pk(2).serialize()];
        let redeem_script: FromChain = Component(
            check_multisig(
                2,
                &[&uncompressed[..], &compressed[0], &compressed[1]],
                false,
            )
            .unwrap(),
        )
        .weaken();
        let taddr =
            TransparentAddress::ScriptHash(crate::util::hash160::hash(&redeem_script.to_bytes()));
        let coin = TxOut::new(Zatoshis::from_u64(10000).unwrap(), taddr.script().into());

        let mut builder = TransparentBuilder::empty();
        builder
            .add_p2sh_input(redeem_script, OutPoint::new([0u8; 32], 0), coin.clone())
            .unwrap();
        let mut bundle = builder.build_for_pczt().unwrap();
        for &i in signers {
            // PCZT signs only with compressed keys, so key 0 cannot add a signature.
            let _ = bundle.inputs_mut()[0].sign(0, |_| [0u8; 32], &sks[i]);
        }
        bundle.finalize_spends()?;

        let checker = CallbackTransactionSignatureChecker {
            sighash: &|_, _| Some([0u8; 32]),
            lock_time: 0,
            is_final: true,
        };
        let script_sig = bundle.inputs[0].script_sig.as_ref().unwrap().to_bytes();
        Ok(
            Raw::from_raw_parts(script_sig, coin.script_pubkey().0.0.clone())
                .eval(Flags::P2SH | Flags::CHECKLOCKTIMEVERIFY, &checker)
                .unwrap(),
        )
    }

    /// The compressed keys can still meet the threshold when the script also has an
    /// uncompressed key.
    #[test]
    fn multisig_finalizes_around_an_uncompressed_key() {
        assert!(matches!(finalize(&[1, 2]), Ok(true)));
        assert!(matches!(
            finalize(&[0, 1]),
            Err(SpendFinalizerError::UncompressedPubkeyInScript)
        ));
    }
}
