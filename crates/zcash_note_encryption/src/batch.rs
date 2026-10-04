//! APIs for batch trial decryption.

use alloc::vec::Vec; // module is alloc only

use crate::{
    BatchDomain, COMPACT_NOTE_SIZE, ENC_CIPHERTEXT_SIZE, EphemeralKeyBytes, ShieldedOutput,
    try_compact_note_decryption_inner, try_note_decryption_inner,
};

/// Trial decryption of a batch of notes with a set of recipients.
///
/// This is the batched version of [`crate::try_note_decryption`].
///
/// Returns a vector containing the decrypted result for each output,
/// with the same length and in the same order as the outputs were
/// provided, along with the index in the `ivks` slice associated with
/// the IVK that successfully decrypted the output.
#[allow(clippy::type_complexity)]
pub fn try_note_decryption<D: BatchDomain, Output: ShieldedOutput<D, ENC_CIPHERTEXT_SIZE>>(
    ivks: &[D::IncomingViewingKey],
    outputs: &[(D, Output)],
) -> Vec<Option<((D::Note, D::Recipient, D::Memo), usize)>> {
    batch_note_decryption(ivks, outputs, try_note_decryption_inner)
}

/// Trial decryption of a batch of notes for light clients with a set of
/// recipients.
///
/// This is the batched version of [`crate::try_compact_note_decryption`].
///
/// Returns a vector containing the decrypted result for each output,
/// with the same length and in the same order as the outputs were
/// provided, along with the index in the `ivks` slice associated with
/// the IVK that successfully decrypted the output.
#[allow(clippy::type_complexity)]
pub fn try_compact_note_decryption<D: BatchDomain, Output: ShieldedOutput<D, COMPACT_NOTE_SIZE>>(
    ivks: &[D::IncomingViewingKey],
    outputs: &[(D, Output)],
) -> Vec<Option<((D::Note, D::Recipient), usize)>> {
    batch_note_decryption(ivks, outputs, try_compact_note_decryption_inner)
}

fn batch_note_decryption<D: BatchDomain, Output: ShieldedOutput<D, CS>, F, FR, const CS: usize>(
    ivks: &[D::IncomingViewingKey],
    outputs: &[(D, Output)],
    decrypt_inner: F,
) -> Vec<Option<(FR, usize)>>
where
    F: Fn(&D, &D::IncomingViewingKey, &EphemeralKeyBytes, &Output, &D::SymmetricKey) -> Option<FR>,
{
    if ivks.is_empty() {
        return (0..outputs.len()).map(|_| None).collect();
    };

    // Fetch the ephemeral keys for each output, and batch-parse and prepare them.
    let ephemeral_keys = D::batch_epk(outputs.iter().map(|(_, output)| output.ephemeral_key()));

    // Derive the shared secrets for all combinations of (ivk, output), one batched
    // same-key agreement per ivk: domains for which same-scalar multiplications can
    // share work accelerate here, and the default `batch_ka_agree_dec` implementation
    // is exactly the previous per-item computation.
    // Reassembly below is in the (output-major, ivk-minor) order the batch-KDF
    // expects, moving values out of the per-ivk columns (`SharedSecret` need not be
    // `Clone`).
    let mut columns: Vec<_> = ivks
        .iter()
        .map(|ivk| {
            D::batch_ka_agree_dec(ivk, ephemeral_keys.iter().map(|(epk, _)| epk.as_ref()))
                .into_iter()
        })
        .collect();
    let mut secrets: Vec<Option<D::SharedSecret>> =
        Vec::with_capacity(ephemeral_keys.len() * ivks.len());
    for _ in 0..ephemeral_keys.len() {
        for column in columns.iter_mut() {
            secrets.push(
                column
                    .next()
                    .expect("all columns have one entry per output"),
            );
        }
    }
    // Preserve the upstream iterator code during the ownership migration.
    #[allow(clippy::manual_repeat_n)]
    let items = secrets.into_iter().zip(
        ephemeral_keys
            .iter()
            .flat_map(|(_, ephemeral_key)| core::iter::repeat(ephemeral_key).take(ivks.len())),
    );

    // Run the batch-KDF to obtain the symmetric keys from the shared secrets.
    let keys = D::batch_kdf(items);

    // Finish the trial decryption!
    keys.chunks(ivks.len())
        .zip(ephemeral_keys.iter().zip(outputs.iter()))
        .map(|(key_chunk, ((_, ephemeral_key), (domain, output)))| {
            key_chunk
                .iter()
                .zip(ivks.iter().enumerate())
                .find_map(|(key, (i, ivk))| {
                    key.as_ref()
                        .and_then(|key| decrypt_inner(domain, ivk, ephemeral_key, output, key))
                        .map(|out| (out, i))
                })
        })
        .collect::<Vec<Option<_>>>()
}
