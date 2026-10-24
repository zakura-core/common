//! One Action's decoded inputs, independent gadget chains, and ordered merge.
//!
//! [`super::build_native_witness_of`] finalizes the returned writer. The
//! prologue and epilogue stay in the same function as chain dispatch, so their
//! statement checks, direct writes, and failure order remain visible together.
//! [`CHAINS`] also supplies the parent entry point's pool-provisioning count.

use sensei_shared::MERKLE_DEPTH;
use sensei_shared::fixed_bases::FixedBase;

use crate::Error;
use crate::native::curve::PallasPoint;
use crate::native::field::{Fp, Fq};
use crate::native::regions::{public_input, roles, sinsemilla_hashes};
use crate::types::{Action, NativeStatement};

use super::decomposition::{write_commit_ivk_decomposition, write_note_decomposition};
use super::fixed_base::{write_full_fixed_mul, write_short_fixed_mul};
use super::poseidon::write_nullifier;
use super::sinsemilla::{write_commit_ivk_sinsemilla, write_merkle_path, write_note_commitment};
use super::variable_base::write_variable_base_mul;
use super::{
    RowMap, WitnessWriter, point_coordinates, require_merkle_root, require_statement_point,
    require_statement_value, require_top_level_relations, signed_difference,
    write_complete_addition, write_direct, write_point,
};

/// The decoded inputs one Action's gadget chains read: everything the
/// schedule derives from the Action and its statement before any gadget
/// runs, moved into the chain wave's tasks.
#[derive(Clone)]
struct ChainInputs {
    instance: NativeStatement,
    psi_old: Fp,
    rho_old: Fp,
    nk: Fp,
    v_old: u64,
    v_new: u64,
    magnitude: Fp,
    sign: Fp,
    cm_old: PallasPoint,
    g_d_old: PallasPoint,
    pk_d_old: PallasPoint,
    rcm_old: Fq,
    ak: PallasPoint,
    alpha: Fq,
    rivk: Fq,
    g_d_new: PallasPoint,
    pk_d_new: PallasPoint,
    psi_new: Fp,
    rcm_new: Fq,
    rcv: Fq,
    merkle_path: [Fp; MERKLE_DEPTH],
    position: u32,
}

/// The six independent gadget chains of one Action's schedule, in the
/// serial schedule's order — the order their results are read in, so the
/// first error is the serial schedule's.
#[derive(Clone, Copy)]
pub(super) enum Chain {
    /// The value commitment: short and full fixed-base products and the
    /// complete addition to `cv_net`, checked against the statement.
    Value,
    /// `rk = [α]G + ak`, checked against the statement.
    Rk,
    /// The viewing-key commitment through `ivk`, the variable-base
    /// `[ivk]g_d_old`, and the `pk_d_old` check and write.
    Ivk,
    /// The old note: decomposition, commitment (checked against `cm_old`)
    /// and nullifier (checked against the statement).
    OldNote,
    /// The Merkle path from `cm_old`'s x-coordinate to the anchor check.
    Merkle,
    /// The new note: its points, decomposition and commitment (checked
    /// against `cmx`).
    NewNote,
}

pub(super) const CHAINS: [Chain; 6] = [
    Chain::Value,
    Chain::Rk,
    Chain::Ivk,
    Chain::OldNote,
    Chain::Merkle,
    Chain::NewNote,
];

/// Runs the fixed writer schedule for one Action into the supplied writer
/// (tests pass a shadowed writer to exercise the enum-cell oracle).
///
/// The prologue (statement decoding and the direct writes) and the epilogue
/// (statement and cross-address rows) run on `writer`; the six gadget
/// chains run as pool tasks on chain writers and merge back in schedule
/// order. Every cell, support bit and error equals the serial
/// schedule's.
pub(super) fn write_native_witness_into<'a>(
    action: &Action,
    statement: &NativeStatement,
    mut writer: WitnessWriter<'a>,
) -> Result<WitnessWriter<'a>, Error> {
    require_top_level_relations(action)?;
    // The native statement record, decoded once by the pipeline: the
    // top-level relations below compare the derived witness values against
    // its named slots.
    let instance = statement;
    let witness = &action.witness;
    let row_map = RowMap::load();

    let psi_old = witness.psi_old.native();
    let rho_old = witness.rho_old.native();
    let nk = witness.nk.native();
    let v_old = <Fp>::from_u64(witness.v_old);
    let v_new = <Fp>::from_u64(witness.v_new);
    let cm_old = witness.cm_old.native();
    let g_d_old = witness.g_d_old.native();
    let pk_d_old = witness.pk_d_old.native();
    let rcm_old = witness.rcm_old.native();
    let ak = witness.ak.native();
    let alpha = witness.alpha.native();
    let rivk = witness.rivk.native();
    let g_d_new = witness.g_d_new.native();
    let pk_d_new = witness.pk_d_new.native();
    let psi_new = witness.psi_new.native();
    let rcm_new = witness.rcm_new.native();
    let rcv = witness.rcv.native();

    write_direct(&mut writer, row_map, 0, roles::PSI_OLD, 0, psi_old)?;
    write_direct(&mut writer, row_map, 0, roles::RHO_OLD, 0, rho_old)?;
    write_point(&mut writer, row_map, roles::CM_OLD, &cm_old)?;
    write_point(&mut writer, row_map, roles::G_D_OLD, &g_d_old)?;
    write_point(&mut writer, row_map, roles::AK, &ak)?;
    write_direct(&mut writer, row_map, 0, roles::NK, 0, nk)?;
    write_direct(&mut writer, row_map, 0, roles::V_OLD, 0, v_old)?;
    write_direct(&mut writer, row_map, 0, roles::V_NEW, 0, v_new)?;

    let (magnitude, sign) = signed_difference(witness.v_old, witness.v_new);
    write_direct(
        &mut writer,
        row_map,
        9,
        roles::VALUE_MAGNITUDE,
        0,
        magnitude,
    )?;
    write_direct(&mut writer, row_map, 9, roles::VALUE_SIGN, 0, sign)?;

    // The authentication path converts into a fixed `MERKLE_DEPTH` array —
    // no vector for the 32 siblings.
    let mut merkle_path = [<Fp>::ZERO; MERKLE_DEPTH];
    for (native, sibling) in merkle_path.iter_mut().zip(&witness.path) {
        *native = sibling.native();
    }
    // The epilogue's cross-address coordinates, taken before the points move
    // into the chain inputs.
    let old_coordinates = point_coordinates(&g_d_old)?;
    let old_pk_coordinates = point_coordinates(&pk_d_old)?;
    let new_coordinates = point_coordinates(&g_d_new)?;
    let new_pk_coordinates = point_coordinates(&pk_d_new)?;
    let inputs = ChainInputs {
        instance: *instance,
        psi_old,
        rho_old,
        nk,
        v_old: witness.v_old,
        v_new: witness.v_new,
        magnitude,
        sign,
        cm_old,
        g_d_old,
        pk_d_old,
        rcm_old,
        ak,
        alpha,
        rivk,
        g_d_new,
        pk_d_new,
        psi_new,
        rcm_new,
        rcv,
        merkle_path,
        position: witness.position,
    };

    // The six chains share no cells (the fixed layout gives each gadget its
    // own regions) and no state beyond the decoded inputs, so they run as
    // one wave; their results are read in schedule order.
    let shadowed = writer.shadowed();
    let target = writer.target;
    let execution = writer.execution;
    let chain_results = execution.map(CHAINS, move |chain, execution| {
        let mut chain_writer = WitnessWriter::chain_writer(target, execution, shadowed);
        let output = run_chain(chain, &inputs, row_map, &mut chain_writer);
        (output, chain_writer)
    });
    let mut root = None;
    for (output, chain_writer) in chain_results {
        if let Some(value) = output? {
            root = Some(value);
        }
        writer.absorb(chain_writer)?;
    }
    let root = root.ok_or(Error::InternalInvariant)?;

    write_direct(&mut writer, row_map, 0, roles::STATEMENT_ROW, 0, v_old)?;
    write_direct(&mut writer, row_map, 1, roles::STATEMENT_ROW, 0, v_new)?;
    write_direct(&mut writer, row_map, 2, roles::STATEMENT_ROW, 0, magnitude)?;
    write_direct(&mut writer, row_map, 3, roles::STATEMENT_ROW, 0, sign)?;
    write_direct(&mut writer, row_map, 4, roles::STATEMENT_ROW, 0, root)?;
    write_direct(
        &mut writer,
        row_map,
        5,
        roles::STATEMENT_ROW,
        0,
        instance[public_input::ANCHOR],
    )?;
    write_direct(
        &mut writer,
        row_map,
        6,
        roles::STATEMENT_ROW,
        0,
        instance[public_input::ENABLE_SPEND],
    )?;
    write_direct(
        &mut writer,
        row_map,
        7,
        roles::STATEMENT_ROW,
        0,
        instance[public_input::ENABLE_OUTPUT],
    )?;

    let disabled = instance[public_input::DISABLE_CROSS_ADDRESS];
    let coordinate_pairs = [
        (old_coordinates.0, new_coordinates.0),
        (old_coordinates.1, new_coordinates.1),
        (old_pk_coordinates.0, new_pk_coordinates.0),
        (old_pk_coordinates.1, new_pk_coordinates.1),
    ];
    for (local_row, (old, new)) in coordinate_pairs.into_iter().enumerate() {
        for column in [0, 2, 8, 9] {
            write_direct(
                &mut writer,
                row_map,
                column,
                roles::CROSS_ADDRESS_ROWS,
                local_row,
                disabled,
            )?;
        }
        write_direct(
            &mut writer,
            row_map,
            1,
            roles::CROSS_ADDRESS_ROWS,
            local_row,
            <Fp>::ZERO,
        )?;
        write_direct(
            &mut writer,
            row_map,
            3,
            roles::CROSS_ADDRESS_ROWS,
            local_row,
            <Fp>::ONE,
        )?;
        write_direct(
            &mut writer,
            row_map,
            4,
            roles::CROSS_ADDRESS_ROWS,
            local_row,
            old,
        )?;
        write_direct(
            &mut writer,
            row_map,
            5,
            roles::CROSS_ADDRESS_ROWS,
            local_row,
            new,
        )?;
        write_direct(
            &mut writer,
            row_map,
            6,
            roles::CROSS_ADDRESS_ROWS,
            local_row,
            <Fp>::ONE,
        )?;
        write_direct(
            &mut writer,
            row_map,
            7,
            roles::CROSS_ADDRESS_ROWS,
            local_row,
            <Fp>::ONE,
        )?;
    }

    Ok(writer)
}

/// Runs one gadget chain of the schedule on its own writer; the Merkle
/// chain returns the root the epilogue writes.
fn run_chain(
    chain: Chain,
    inputs: &ChainInputs,
    row_map: &RowMap,
    writer: &mut WitnessWriter,
) -> Result<Option<Fp>, Error> {
    let instance = &inputs.instance;
    match chain {
        Chain::Value => {
            let value_commitment = write_short_fixed_mul(
                writer,
                row_map,
                roles::VALUE_COMMIT_V.0,
                roles::VALUE_COMMIT_V.1,
                FixedBase::ValueCommitV,
                &inputs.magnitude,
                &inputs.sign,
            )?;
            let value_blind = write_full_fixed_mul(
                writer,
                row_map,
                roles::VALUE_COMMIT_R.0,
                roles::VALUE_COMMIT_R.1,
                FixedBase::ValueCommitR,
                &inputs.rcv,
            )?;
            let cv_net = write_complete_addition(
                writer,
                row_map,
                roles::VALUE_COMMIT_ADDITION,
                &value_commitment,
                &value_blind,
            )?;
            require_statement_point(
                &cv_net,
                &instance[public_input::CV_NET_X],
                &instance[public_input::CV_NET_Y],
            )?;
            Ok(None)
        }
        Chain::Rk => {
            let alpha_commitment = write_full_fixed_mul(
                writer,
                row_map,
                roles::SPEND_AUTH_G.0,
                roles::SPEND_AUTH_G.1,
                FixedBase::SpendAuthG,
                &inputs.alpha,
            )?;
            let rk = write_complete_addition(
                writer,
                row_map,
                roles::RK_ADDITION,
                &alpha_commitment,
                &inputs.ak,
            )?;
            require_statement_point(
                &rk,
                &instance[public_input::RK_X],
                &instance[public_input::RK_Y],
            )?;
            Ok(None)
        }
        Chain::Ivk => {
            write_commit_ivk_decomposition(writer, row_map, &inputs.ak, &inputs.nk)?;
            let rivk_commitment = write_full_fixed_mul(
                writer,
                row_map,
                roles::COMMIT_IVK_R.0,
                roles::COMMIT_IVK_R.1,
                FixedBase::CommitIvkR,
                &inputs.rivk,
            )?;
            let commit_ivk_m =
                write_commit_ivk_sinsemilla(writer, row_map, &inputs.ak, &inputs.nk)?;
            let commit_ivk = write_complete_addition(
                writer,
                row_map,
                roles::COMMIT_IVK_ADDITION,
                &commit_ivk_m,
                &rivk_commitment,
            )?;
            let (ivk, _) = point_coordinates(&commit_ivk)?;
            let derived_pk_d_old = write_variable_base_mul(writer, row_map, &inputs.g_d_old, &ivk)?;
            if derived_pk_d_old != inputs.pk_d_old {
                return Err(Error::UnsatisfiedWitness);
            }
            write_point(writer, row_map, roles::PK_D_OLD, &inputs.pk_d_old)?;
            Ok(None)
        }
        Chain::OldNote => {
            let old_note = write_note_decomposition(
                writer,
                row_map,
                roles::NOTE_DECOMPOSITION_OLD,
                6,
                &inputs.g_d_old,
                &inputs.pk_d_old,
                inputs.v_old,
                &inputs.rho_old,
                &inputs.psi_old,
            )?;
            let derived_cm_old = write_note_commitment(
                writer,
                row_map,
                roles::NOTE_COMMIT_R_OLD.0,
                roles::NOTE_COMMIT_R_OLD.1,
                sinsemilla_hashes::OLD_NOTE_HASH_REGION,
                roles::NOTE_COMMIT_ADDITION_OLD,
                0,
                &old_note,
                &inputs.rcm_old,
            )?;
            if derived_cm_old != inputs.cm_old {
                return Err(Error::UnsatisfiedWitness);
            }
            let nf_old = write_nullifier(
                writer,
                row_map,
                &inputs.nk,
                &inputs.rho_old,
                &inputs.psi_old,
                &inputs.cm_old,
            )?;
            require_statement_value(&nf_old, &instance[public_input::NF_OLD])?;
            Ok(None)
        }
        Chain::Merkle => {
            // The leaf is the statement's own `cm_old`: the old-note chain
            // requires the derived commitment to equal it, and its error is
            // read first, so the two leaves are the same value wherever this
            // result is used.
            let old_cmx = point_coordinates(&inputs.cm_old)?.0;
            let root = write_merkle_path(
                writer,
                row_map,
                &old_cmx,
                &inputs.merkle_path,
                inputs.position,
            )?;
            require_merkle_root(inputs.v_old, &root, &instance[public_input::ANCHOR])?;
            Ok(Some(root))
        }
        Chain::NewNote => {
            write_point(writer, row_map, roles::G_D_NEW, &inputs.g_d_new)?;
            write_point(writer, row_map, roles::PK_D_NEW, &inputs.pk_d_new)?;
            write_direct(writer, row_map, 0, roles::PSI_NEW, 0, inputs.psi_new)?;
            let new_note = write_note_decomposition(
                writer,
                row_map,
                roles::NOTE_DECOMPOSITION_NEW,
                7,
                &inputs.g_d_new,
                &inputs.pk_d_new,
                inputs.v_new,
                &instance[public_input::NF_OLD],
                &inputs.psi_new,
            )?;
            let derived_cm_new = write_note_commitment(
                writer,
                row_map,
                roles::NOTE_COMMIT_R_NEW.0,
                roles::NOTE_COMMIT_R_NEW.1,
                sinsemilla_hashes::NEW_NOTE_HASH_REGION,
                roles::NOTE_COMMIT_ADDITION_NEW,
                5,
                &new_note,
                &inputs.rcm_new,
            )?;
            require_statement_value(
                &point_coordinates(&derived_cm_new)?.0,
                &instance[public_input::CMX],
            )?;
            Ok(None)
        }
    }
}
