//! Experimental, borrowed reader for the Zcash transaction wire format.
//!
//! [`TransactionView`] checks that a byte string is a *structurally* valid
//! encoding of a version 1 to 6 transaction and exposes its fields as borrowed
//! slices of the input, together with the exact transaction ID.
//!
//! # Trust boundary
//!
//! A successful parse means only that the bytes follow the wire grammar. The
//! reader checks canonical CompactSize encodings, the version, version group and
//! branch ID combination, amount ranges, field lengths, per-pool flag and proof
//! length rules, and exact transaction boundaries. It deliberately does **not**
//! check:
//!
//! - that commitments, keys, nullifiers or ephemeral keys are valid curve points
//!   or canonical field elements (Common's typed decoder rejects some of these;
//!   this reader accepts them);
//! - proofs or signatures;
//! - contextual consensus rules: whether the branch ID matches the block height,
//!   whether value balances sum to a non-negative fee, coinbase rules, script
//!   validity, expiry, or whether inputs exist.
//!
//! Callers must not treat a parsed transaction as a valid one. A transaction
//! that reaches this reader from a node's block or mempool was already
//! validated by that node; one from anywhere else has not been.
//!
//! The transaction ID is computed from the parsed fields with SHA-256d for
//! versions 1 to 4 and the ZIP 244 / ZIP 229 BLAKE2b tree for versions 5 and 6.
#![no_std]
#![deny(missing_docs)]

extern crate alloc;

use alloc::vec::Vec;

use zcash_protocol::{
    consensus::BranchId,
    constants::{
        V3_TX_VERSION, V3_VERSION_GROUP_ID, V4_TX_VERSION, V4_VERSION_GROUP_ID, V5_TX_VERSION,
        V5_VERSION_GROUP_ID, V6_TX_VERSION, V6_VERSION_GROUP_ID,
    },
    consensus::OrchardProtocolRevision,
    value::{ZatBalance, Zatoshis},
};

mod error;
mod reader;
mod txid;

pub use error::DecodeError;
use reader::Reader;

/// The size of a Groth16 proof (Sapling, and Sprout in v4 transactions).
pub const GROTH_PROOF_SIZE: usize = 192;
/// The size of a PHGR13 proof (Sprout in v2 and v3 transactions).
pub const PHGR_PROOF_SIZE: usize = 296;
/// The size of a Sapling or Orchard-protocol note ciphertext.
pub const ENC_CIPHERTEXT_SIZE: usize = 580;
/// The size of a Sapling or Orchard-protocol outgoing ciphertext.
pub const OUT_CIPHERTEXT_SIZE: usize = 80;
/// The size of a Sprout note ciphertext.
pub const SPROUT_CIPHERTEXT_SIZE: usize = 601;

const OUTPOINT_SIZE: usize = 36;
/// prevout + empty script length + sequence.
const MIN_TX_IN_SIZE: usize = OUTPOINT_SIZE + 1 + 4;
/// value + empty script length.
const MIN_TX_OUT_SIZE: usize = 8 + 1;
const JOINSPLIT_FIXED_SIZE: usize = 8 + 8 + 32 + 2 * 32 + 2 * 32 + 32 + 32 + 2 * 32;
const JOINSPLIT_CIPHERTEXTS_SIZE: usize = 2 * SPROUT_CIPHERTEXT_SIZE;
const SAPLING_SPEND_V4_SIZE: usize = 32 * 4 + GROTH_PROOF_SIZE + 64;
const SAPLING_OUTPUT_V4_SIZE: usize =
    32 * 3 + ENC_CIPHERTEXT_SIZE + OUT_CIPHERTEXT_SIZE + GROTH_PROOF_SIZE;
const SAPLING_SPEND_V5_SIZE: usize = 32 * 3;
const SAPLING_OUTPUT_V5_SIZE: usize = 32 * 3 + ENC_CIPHERTEXT_SIZE + OUT_CIPHERTEXT_SIZE;
const ACTION_SIZE: usize = 32 * 5 + ENC_CIPHERTEXT_SIZE + OUT_CIPHERTEXT_SIZE;

/// Orchard-protocol proof length: a fixed base plus a fixed size per action.
/// Mirrors `orchard::Proof::expected_proof_size`.
const ACTION_PROOF_BASE_SIZE: usize = 2720;
const ACTION_PROOF_PER_ACTION_SIZE: usize = 2272;

const FLAG_SPENDS_ENABLED: u8 = 0b0000_0001;
const FLAG_OUTPUTS_ENABLED: u8 = 0b0000_0010;
const FLAG_CROSS_ADDRESS_ENABLED: u8 = 0b0000_0100;
const FLAGS_ALWAYS_UNSET: u8 = !0b0000_0111;

/// A supported transaction format version.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TxVersion {
    /// Pre-Overwinter version 1: transparent only.
    V1,
    /// Pre-Overwinter version 2: adds Sprout JoinSplits with PHGR13 proofs.
    V2,
    /// Overwinter version 3: adds the version group ID and expiry height.
    V3,
    /// Sapling version 4: adds Sapling; Sprout proofs become Groth16.
    V4,
    /// NU5 version 5 (ZIP 225): adds the branch ID and Orchard; drops Sprout.
    V5,
    /// Version 6 (ZIP 229): adds the Ironwood pool.
    V6,
}

impl TxVersion {
    /// The transaction version number (1 to 6).
    pub fn number(self) -> u32 {
        match self {
            TxVersion::V1 => 1,
            TxVersion::V2 => 2,
            TxVersion::V3 => V3_TX_VERSION,
            TxVersion::V4 => V4_TX_VERSION,
            TxVersion::V5 => V5_TX_VERSION,
            TxVersion::V6 => V6_TX_VERSION,
        }
    }

    /// The four-byte header: the version number with the overwintered bit for v3+.
    pub fn header(self) -> u32 {
        match self {
            TxVersion::V1 | TxVersion::V2 => self.number(),
            _ => self.number() | (1 << 31),
        }
    }

    /// The version group ID, for overwintered versions.
    pub fn version_group_id(self) -> Option<u32> {
        match self {
            TxVersion::V1 | TxVersion::V2 => None,
            TxVersion::V3 => Some(V3_VERSION_GROUP_ID),
            TxVersion::V4 => Some(V4_VERSION_GROUP_ID),
            TxVersion::V5 => Some(V5_VERSION_GROUP_ID),
            TxVersion::V6 => Some(V6_VERSION_GROUP_ID),
        }
    }

    fn has_sprout(self) -> bool {
        matches!(self, TxVersion::V2 | TxVersion::V3 | TxVersion::V4)
    }

    /// Whether the transaction ID is SHA-256d of the encoding (versions 1 to 4).
    fn has_legacy_txid(self) -> bool {
        self <= TxVersion::V4
    }

    /// Mirrors `zakura_primitives::transaction::TxVersion::valid_in_branch` for v5/v6.
    fn valid_in_branch(self, branch: BranchId) -> bool {
        use BranchId::*;
        match self {
            TxVersion::V5 => match branch {
                Sprout | Overwinter | Sapling | Blossom | Heartwood | Canopy => false,
                Nu5 | Nu6 | Nu6_1 | Nu6_2 | Nu6_3 | Nu7 => true,
            },
            TxVersion::V6 => match branch {
                Sprout | Overwinter | Sapling | Blossom | Heartwood | Canopy | Nu5 | Nu6
                | Nu6_1 | Nu6_2 => false,
                Nu6_3 | Nu7 => true,
            },
            // Earlier versions carry no branch ID.
            _ => true,
        }
    }
}

/// A transparent input. `script_sig` is the raw unparsed script.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TransparentInput<'a> {
    /// The previous transaction ID, in protocol (internal) byte order.
    pub prevout_txid: &'a [u8; 32],
    /// The previous output index.
    pub prevout_index: u32,
    /// The raw input script.
    pub script_sig: &'a [u8],
    /// The sequence number.
    pub sequence: u32,
}

impl TransparentInput<'_> {
    /// Whether this input has the null outpoint that marks a coinbase input.
    pub fn is_null_prevout(&self) -> bool {
        self.prevout_txid == &[0; 32] && self.prevout_index == u32::MAX
    }
}

/// A transparent output. `script_pubkey` is the raw unparsed script.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TransparentOutput<'a> {
    /// The output value, in `0..=MAX_MONEY`.
    pub value: Zatoshis,
    /// The raw output script.
    pub script_pubkey: &'a [u8],
}

/// A Sprout JoinSplit description.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JoinSplit<'a> {
    /// Value leaving the transparent pool into Sprout, in `0..=MAX_MONEY`.
    pub vpub_old: Zatoshis,
    /// Value entering the transparent pool from Sprout, in `0..=MAX_MONEY`.
    pub vpub_new: Zatoshis,
    /// The Sprout note commitment tree anchor.
    pub anchor: &'a [u8; 32],
    /// The two input nullifiers.
    pub nullifiers: [&'a [u8; 32]; 2],
    /// The two output note commitments.
    pub commitments: [&'a [u8; 32]; 2],
    /// The ephemeral key.
    pub ephemeral_key: &'a [u8; 32],
    /// The random seed.
    pub random_seed: &'a [u8; 32],
    /// The two MACs.
    pub macs: [&'a [u8; 32]; 2],
    /// The proof: PHGR13 (296 bytes) in v2/v3, Groth16 (192 bytes) in v4.
    pub proof: &'a [u8],
    /// The two output note ciphertexts.
    pub ciphertexts: [&'a [u8; SPROUT_CIPHERTEXT_SIZE]; 2],
}

/// The Sprout JoinSplits of a v2, v3 or v4 transaction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SproutBundle<'a> {
    /// The JoinSplit descriptions; never empty.
    pub joinsplits: Vec<JoinSplit<'a>>,
    /// The JoinSplit signature verification key.
    pub joinsplit_pubkey: &'a [u8; 32],
    /// The JoinSplit signature.
    pub joinsplit_sig: &'a [u8; 64],
}

/// A Sapling spend description.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SaplingSpend<'a> {
    /// The value commitment.
    pub cv: &'a [u8; 32],
    /// The anchor: per spend in v4, shared by all spends in v5/v6.
    pub anchor: &'a [u8; 32],
    /// The nullifier.
    pub nullifier: &'a [u8; 32],
    /// The randomized validating key.
    pub rk: &'a [u8; 32],
    /// The Groth16 proof.
    pub zkproof: &'a [u8; GROTH_PROOF_SIZE],
    /// The spend authorization signature.
    pub spend_auth_sig: &'a [u8; 64],
}

/// A Sapling output description.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SaplingOutput<'a> {
    /// The value commitment.
    pub cv: &'a [u8; 32],
    /// The note commitment u-coordinate.
    pub cmu: &'a [u8; 32],
    /// The ephemeral public key.
    pub ephemeral_key: &'a [u8; 32],
    /// The note ciphertext.
    pub enc_ciphertext: &'a [u8; ENC_CIPHERTEXT_SIZE],
    /// The outgoing ciphertext.
    pub out_ciphertext: &'a [u8; OUT_CIPHERTEXT_SIZE],
    /// The Groth16 proof.
    pub zkproof: &'a [u8; GROTH_PROOF_SIZE],
}

/// A Sapling bundle with at least one spend or output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaplingBundle<'a> {
    /// The spend descriptions.
    pub spends: Vec<SaplingSpend<'a>>,
    /// The output descriptions.
    pub outputs: Vec<SaplingOutput<'a>>,
    /// The Sapling value balance, in `-MAX_MONEY..=MAX_MONEY`.
    pub value_balance: ZatBalance,
    /// The binding signature.
    pub binding_sig: &'a [u8; 64],
}

/// Which Orchard-protocol pool an action bundle belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ActionPool {
    /// The Orchard pool (v5 and v6).
    Orchard,
    /// The Ironwood pool (v6 only).
    Ironwood,
}

impl ActionPool {
    fn name(self) -> &'static str {
        match self {
            ActionPool::Orchard => "Orchard",
            ActionPool::Ironwood => "Ironwood",
        }
    }
}

/// An Orchard or Ironwood action description.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Action<'a> {
    /// The value commitment.
    pub cv: &'a [u8; 32],
    /// The nullifier.
    pub nullifier: &'a [u8; 32],
    /// The randomized validating key.
    pub rk: &'a [u8; 32],
    /// The extracted note commitment.
    pub cmx: &'a [u8; 32],
    /// The ephemeral public key.
    pub ephemeral_key: &'a [u8; 32],
    /// The note ciphertext.
    pub enc_ciphertext: &'a [u8; ENC_CIPHERTEXT_SIZE],
    /// The outgoing ciphertext.
    pub out_ciphertext: &'a [u8; OUT_CIPHERTEXT_SIZE],
    /// The spend authorization signature.
    pub spend_auth_sig: &'a [u8; 64],
}

/// An Orchard or Ironwood bundle with at least one action.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionBundle<'a> {
    /// The pool this bundle belongs to.
    pub pool: ActionPool,
    /// The action descriptions; never empty.
    pub actions: Vec<Action<'a>>,
    /// The raw flags byte. Bits 3..=7 are zero; bit 2 (cross-address) is set only for Ironwood.
    pub flags: u8,
    /// The pool value balance, in `-MAX_MONEY..=MAX_MONEY`.
    pub value_balance: ZatBalance,
    /// The commitment tree anchor.
    pub anchor: &'a [u8; 32],
    /// The aggregated proof.
    pub proof: &'a [u8],
    /// The binding signature.
    pub binding_sig: &'a [u8; 64],
}

impl ActionBundle<'_> {
    /// Whether the spends-enabled flag is set.
    pub fn spends_enabled(&self) -> bool {
        self.flags & FLAG_SPENDS_ENABLED != 0
    }

    /// Whether the outputs-enabled flag is set.
    pub fn outputs_enabled(&self) -> bool {
        self.flags & FLAG_OUTPUTS_ENABLED != 0
    }
}

/// A structurally valid transaction encoding, borrowed from its input bytes.
///
/// See the [crate documentation](crate) for what is and is not checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransactionView<'a> {
    raw: &'a [u8],
    version: TxVersion,
    branch_id: Option<BranchId>,
    lock_time: u32,
    expiry_height: Option<u32>,
    transparent_inputs: Vec<TransparentInput<'a>>,
    transparent_outputs: Vec<TransparentOutput<'a>>,
    sprout: Option<SproutBundle<'a>>,
    sapling: Option<SaplingBundle<'a>>,
    orchard: Option<ActionBundle<'a>>,
    ironwood: Option<ActionBundle<'a>>,
}

impl<'a> TransactionView<'a> {
    /// Parses one transaction from the start of `input` and returns it with the
    /// bytes that follow it (for example, the next transaction in a block).
    pub fn parse_prefix(input: &'a [u8]) -> Result<(Self, &'a [u8]), DecodeError> {
        let mut r = Reader::new(input);
        let view = Self::read(&mut r, input)?;
        Ok((view, &input[r.position()..]))
    }

    /// Parses `input` as exactly one transaction, rejecting trailing bytes.
    pub fn parse_exact(input: &'a [u8]) -> Result<Self, DecodeError> {
        let (view, rest) = Self::parse_prefix(input)?;
        if rest.is_empty() {
            Ok(view)
        } else {
            Err(DecodeError::TrailingBytes { count: rest.len() })
        }
    }

    fn read(r: &mut Reader<'a>, input: &'a [u8]) -> Result<Self, DecodeError> {
        let version = read_version(r)?;
        let mut view = TransactionView {
            raw: &[],
            version,
            branch_id: None,
            lock_time: 0,
            expiry_height: None,
            transparent_inputs: Vec::new(),
            transparent_outputs: Vec::new(),
            sprout: None,
            sapling: None,
            orchard: None,
            ironwood: None,
        };
        if version.has_legacy_txid() {
            view.read_v1_to_v4(r)?;
        } else {
            view.read_v5_v6(r)?;
        }
        view.raw = &input[..r.position()];
        Ok(view)
    }

    fn read_v1_to_v4(&mut self, r: &mut Reader<'a>) -> Result<(), DecodeError> {
        let version = self.version;
        self.read_transparent(r)?;
        self.lock_time = r.u32_le("lock_time")?;
        if version >= TxVersion::V3 {
            self.expiry_height = Some(r.u32_le("expiry_height")?);
        }

        let mut sapling_balance = None;
        let mut spends = Vec::new();
        let mut outputs = Vec::new();
        if version == TxVersion::V4 {
            sapling_balance = Some(read_balance(r, "Sapling value balance")?);
            let n = r.count("Sapling spends", SAPLING_SPEND_V4_SIZE)?;
            spends = r.elements(n, read_spend_v4)?;
            let n = r.count("Sapling outputs", SAPLING_OUTPUT_V4_SIZE)?;
            outputs = r.elements(n, |r| read_output(r, None))?;
        }

        if version.has_sprout() {
            let proof_size = if version == TxVersion::V4 {
                GROTH_PROOF_SIZE
            } else {
                PHGR_PROOF_SIZE
            };
            let n = r.count(
                "JoinSplits",
                JOINSPLIT_FIXED_SIZE + proof_size + JOINSPLIT_CIPHERTEXTS_SIZE,
            )?;
            if n > 0 {
                let joinsplits = r.elements(n, |r| read_joinsplit(r, proof_size))?;
                self.sprout = Some(SproutBundle {
                    joinsplits,
                    joinsplit_pubkey: r.array("joinSplitPubKey")?,
                    joinsplit_sig: r.array("joinSplitSig")?,
                });
            }
        }

        if let Some(value_balance) = sapling_balance {
            if spends.is_empty() && outputs.is_empty() {
                if value_balance != ZatBalance::zero() {
                    return Err(DecodeError::NonZeroBalanceWithoutDescriptions);
                }
            } else {
                self.sapling = Some(SaplingBundle {
                    spends,
                    outputs,
                    value_balance,
                    binding_sig: r.array("Sapling bindingSig")?,
                });
            }
        }
        Ok(())
    }

    fn read_v5_v6(&mut self, r: &mut Reader<'a>) -> Result<(), DecodeError> {
        let raw_branch = r.u32_le("consensus branch ID")?;
        let branch =
            BranchId::try_from(raw_branch).map_err(|_| DecodeError::UnknownBranchId(raw_branch))?;
        if !self.version.valid_in_branch(branch) {
            return Err(DecodeError::VersionNotValidInBranch {
                version: self.version.number(),
                branch_id: raw_branch,
            });
        }
        self.branch_id = Some(branch);
        self.lock_time = r.u32_le("lock_time")?;
        self.expiry_height = Some(r.u32_le("expiry_height")?);
        self.read_transparent(r)?;
        self.sapling = read_sapling_v5(r)?;
        self.orchard = read_action_bundle(r, branch, ActionPool::Orchard)?;
        if self.version == TxVersion::V6 {
            self.ironwood = read_action_bundle(r, branch, ActionPool::Ironwood)?;
        }
        Ok(())
    }

    fn read_transparent(&mut self, r: &mut Reader<'a>) -> Result<(), DecodeError> {
        let n = r.count("transparent inputs", MIN_TX_IN_SIZE)?;
        self.transparent_inputs = r.elements(n, |r| {
            Ok(TransparentInput {
                prevout_txid: r.array("prevout txid")?,
                prevout_index: r.u32_le("prevout index")?,
                script_sig: r.var_bytes("scriptSig")?,
                sequence: r.u32_le("sequence")?,
            })
        })?;
        let n = r.count("transparent outputs", MIN_TX_OUT_SIZE)?;
        self.transparent_outputs = r.elements(n, |r| {
            let value = Zatoshis::from_nonnegative_i64_le_bytes(r.le_bytes8("output value")?)
                .map_err(|_| DecodeError::ValueOutOfRange {
                    field: "transparent output value",
                })?;
            Ok(TransparentOutput {
                value,
                script_pubkey: r.var_bytes("scriptPubKey")?,
            })
        })?;
        Ok(())
    }

    /// The exact bytes of this transaction's encoding.
    pub fn raw(&self) -> &'a [u8] {
        self.raw
    }

    /// The transaction format version.
    pub fn version(&self) -> TxVersion {
        self.version
    }

    /// The consensus branch ID embedded in v5 and v6 transactions; `None` for v1 to v4.
    pub fn branch_id(&self) -> Option<BranchId> {
        self.branch_id
    }

    /// The lock time.
    pub fn lock_time(&self) -> u32 {
        self.lock_time
    }

    /// The expiry height for v3 and later; `None` for v1 and v2.
    pub fn expiry_height(&self) -> Option<u32> {
        self.expiry_height
    }

    /// The transparent inputs, including their raw scripts.
    pub fn transparent_inputs(&self) -> &[TransparentInput<'a>] {
        &self.transparent_inputs
    }

    /// The transparent outputs.
    pub fn transparent_outputs(&self) -> &[TransparentOutput<'a>] {
        &self.transparent_outputs
    }

    /// Whether this has the shape of a coinbase transaction: exactly one input,
    /// with the null outpoint. Coinbase consensus rules are not checked.
    pub fn is_coinbase(&self) -> bool {
        matches!(self.transparent_inputs.as_slice(), [input] if input.is_null_prevout())
    }

    /// The Sprout JoinSplits, if any.
    pub fn sprout(&self) -> Option<&SproutBundle<'a>> {
        self.sprout.as_ref()
    }

    /// The Sapling bundle, if it has any spends or outputs.
    pub fn sapling(&self) -> Option<&SaplingBundle<'a>> {
        self.sapling.as_ref()
    }

    /// The Orchard bundle, if it has any actions.
    pub fn orchard(&self) -> Option<&ActionBundle<'a>> {
        self.orchard.as_ref()
    }

    /// The Ironwood bundle, if it has any actions (v6 only).
    pub fn ironwood(&self) -> Option<&ActionBundle<'a>> {
        self.ironwood.as_ref()
    }

    /// Whether any shielded pool has descriptions.
    pub fn has_shielded_components(&self) -> bool {
        self.sprout.is_some()
            || self.sapling.is_some()
            || self.orchard.is_some()
            || self.ironwood.is_some()
    }

    /// The net value the Sprout JoinSplits move into the transparent pool,
    /// `sum(vpub_new) - sum(vpub_old)`. Zero without JoinSplits.
    ///
    /// Returns `None` if a partial sum leaves `-MAX_MONEY..=MAX_MONEY`, matching
    /// `zakura_primitives::transaction::components::sprout::Bundle::value_balance`.
    pub fn sprout_value_balance(&self) -> Option<ZatBalance> {
        self.sprout.as_ref().map_or(Some(ZatBalance::zero()), |b| {
            b.joinsplits.iter().try_fold(ZatBalance::zero(), |total, js| {
                let net = (ZatBalance::from(js.vpub_new) - ZatBalance::from(js.vpub_old))?;
                total + net
            })
        })
    }

    /// The Sapling value balance; zero without a Sapling bundle.
    pub fn sapling_value_balance(&self) -> ZatBalance {
        self.sapling
            .as_ref()
            .map_or(ZatBalance::zero(), |b| b.value_balance)
    }

    /// The Orchard value balance; zero without an Orchard bundle.
    pub fn orchard_value_balance(&self) -> ZatBalance {
        self.orchard
            .as_ref()
            .map_or(ZatBalance::zero(), |b| b.value_balance)
    }

    /// The Ironwood value balance; zero without an Ironwood bundle.
    pub fn ironwood_value_balance(&self) -> ZatBalance {
        self.ironwood
            .as_ref()
            .map_or(ZatBalance::zero(), |b| b.value_balance)
    }

    /// The transaction ID in protocol (internal) byte order; reverse it for the
    /// conventional hex display.
    pub fn txid(&self) -> [u8; 32] {
        txid::txid(self)
    }
}

fn read_version(r: &mut Reader<'_>) -> Result<TxVersion, DecodeError> {
    let header = r.u32_le("header")?;
    let overwintered = header >> 31 == 1;
    let number = header & 0x7FFF_FFFF;
    if !overwintered {
        return match number {
            1 => Ok(TxVersion::V1),
            2 => Ok(TxVersion::V2),
            _ => Err(DecodeError::UnsupportedVersion {
                header,
                version_group_id: None,
            }),
        };
    }
    let group = r.u32_le("version group ID")?;
    match (number, group) {
        (V3_TX_VERSION, V3_VERSION_GROUP_ID) => Ok(TxVersion::V3),
        (V4_TX_VERSION, V4_VERSION_GROUP_ID) => Ok(TxVersion::V4),
        (V5_TX_VERSION, V5_VERSION_GROUP_ID) => Ok(TxVersion::V5),
        (V6_TX_VERSION, V6_VERSION_GROUP_ID) => Ok(TxVersion::V6),
        _ => Err(DecodeError::UnsupportedVersion {
            header,
            version_group_id: Some(group),
        }),
    }
}

fn read_balance(r: &mut Reader<'_>, field: &'static str) -> Result<ZatBalance, DecodeError> {
    ZatBalance::from_i64_le_bytes(r.le_bytes8(field)?)
        .map_err(|_| DecodeError::ValueOutOfRange { field })
}

fn read_vpub(r: &mut Reader<'_>, field: &'static str) -> Result<Zatoshis, DecodeError> {
    Zatoshis::from_u64_le_bytes(r.le_bytes8(field)?)
        .map_err(|_| DecodeError::ValueOutOfRange { field })
}

fn read_joinsplit<'a>(r: &mut Reader<'a>, proof_size: usize) -> Result<JoinSplit<'a>, DecodeError> {
    Ok(JoinSplit {
        vpub_old: read_vpub(r, "vpub_old")?,
        vpub_new: read_vpub(r, "vpub_new")?,
        anchor: r.array("JoinSplit anchor")?,
        nullifiers: [r.array("JoinSplit nullifier")?, r.array("JoinSplit nullifier")?],
        commitments: [r.array("JoinSplit commitment")?, r.array("JoinSplit commitment")?],
        ephemeral_key: r.array("JoinSplit ephemeral key")?,
        random_seed: r.array("JoinSplit random seed")?,
        macs: [r.array("JoinSplit MAC")?, r.array("JoinSplit MAC")?],
        proof: r.take(proof_size, "JoinSplit proof")?,
        ciphertexts: [
            r.array("JoinSplit ciphertext")?,
            r.array("JoinSplit ciphertext")?,
        ],
    })
}

fn read_spend_v4<'a>(r: &mut Reader<'a>) -> Result<SaplingSpend<'a>, DecodeError> {
    Ok(SaplingSpend {
        cv: r.array("Sapling spend cv")?,
        anchor: r.array("Sapling spend anchor")?,
        nullifier: r.array("Sapling spend nullifier")?,
        rk: r.array("Sapling spend rk")?,
        zkproof: r.array("Sapling spend proof")?,
        spend_auth_sig: r.array("Sapling spend signature")?,
    })
}

/// Reads a Sapling output; v4 outputs carry their proof inline (`proof` is `None`),
/// v5/v6 outputs get it later from the proofs array.
fn read_output<'a>(
    r: &mut Reader<'a>,
    proof: Option<&'a [u8; GROTH_PROOF_SIZE]>,
) -> Result<SaplingOutput<'a>, DecodeError> {
    let cv = r.array("Sapling output cv")?;
    let cmu = r.array("Sapling output cmu")?;
    let ephemeral_key = r.array("Sapling output ephemeral key")?;
    let enc_ciphertext = r.array("Sapling output enc_ciphertext")?;
    let out_ciphertext = r.array("Sapling output out_ciphertext")?;
    let zkproof = match proof {
        Some(p) => p,
        None => r.array("Sapling output proof")?,
    };
    Ok(SaplingOutput {
        cv,
        cmu,
        ephemeral_key,
        enc_ciphertext,
        out_ciphertext,
        zkproof,
    })
}

const ZERO_PROOF: [u8; GROTH_PROOF_SIZE] = [0; GROTH_PROOF_SIZE];
const ZERO_32: [u8; 32] = [0; 32];
const ZERO_64: [u8; 64] = [0; 64];

/// Reads the v5/v6 Sapling bundle (ZIP 225 layout, shared by ZIP 229).
fn read_sapling_v5<'a>(r: &mut Reader<'a>) -> Result<Option<SaplingBundle<'a>>, DecodeError> {
    // Spend and output descriptions come first without their proofs and
    // signatures; those follow in separate arrays and are attached afterwards.
    let n_spends = r.count("Sapling spends", SAPLING_SPEND_V5_SIZE)?;
    let mut spends = r.elements(n_spends, |r| {
        Ok(SaplingSpend {
            cv: r.array("Sapling spend cv")?,
            nullifier: r.array("Sapling spend nullifier")?,
            rk: r.array("Sapling spend rk")?,
            anchor: &ZERO_32,
            zkproof: &ZERO_PROOF,
            spend_auth_sig: &ZERO_64,
        })
    })?;
    let n_outputs = r.count("Sapling outputs", SAPLING_OUTPUT_V5_SIZE)?;
    let mut outputs = r.elements(n_outputs, |r| read_output(r, Some(&ZERO_PROOF)))?;
    if n_spends == 0 && n_outputs == 0 {
        return Ok(None);
    }
    let value_balance = read_balance(r, "Sapling value balance")?;
    if n_spends > 0 {
        let anchor = r.array("Sapling anchor")?;
        for spend in &mut spends {
            spend.anchor = anchor;
        }
    }
    for spend in &mut spends {
        spend.zkproof = r.array("Sapling spend proof")?;
    }
    for spend in &mut spends {
        spend.spend_auth_sig = r.array("Sapling spend signature")?;
    }
    for output in &mut outputs {
        output.zkproof = r.array("Sapling output proof")?;
    }
    Ok(Some(SaplingBundle {
        spends,
        outputs,
        value_balance,
        binding_sig: r.array("Sapling bindingSig")?,
    }))
}

/// Reads an Orchard-protocol bundle for `pool` under `branch`.
///
/// Mirrors `zakura_primitives::transaction::components::orchard::read_bundle` and
/// `bundle_version_for_branch`: the pool must be active under the branch, flag
/// bits 3..=7 must be zero, bit 2 may be set only for Ironwood, and the proof must
/// have the canonical length except for the historical Orchard pool before NU6.2.
fn read_action_bundle<'a>(
    r: &mut Reader<'a>,
    branch: BranchId,
    pool: ActionPool,
) -> Result<Option<ActionBundle<'a>>, DecodeError> {
    let n = r.count("actions", ACTION_SIZE)?;
    if n == 0 {
        return Ok(None);
    }
    let mut actions = r.elements(n, |r| {
        Ok(Action {
            cv: r.array("action cv")?,
            nullifier: r.array("action nullifier")?,
            rk: r.array("action rk")?,
            cmx: r.array("action cmx")?,
            ephemeral_key: r.array("action ephemeral key")?,
            enc_ciphertext: r.array("action enc_ciphertext")?,
            out_ciphertext: r.array("action out_ciphertext")?,
            spend_auth_sig: &ZERO_64,
        })
    })?;

    let revision = branch.orchard_protocol_revision();
    let enforce_proof_size = match (pool, revision) {
        (_, None) | (ActionPool::Ironwood, Some(OrchardProtocolRevision::InsecureV1))
        | (ActionPool::Ironwood, Some(OrchardProtocolRevision::V2)) => {
            return Err(DecodeError::PoolNotActive { pool: pool.name() });
        }
        (ActionPool::Orchard, Some(OrchardProtocolRevision::InsecureV1)) => false,
        (_, Some(_)) => true,
    };

    let flags = r.u8("flags")?;
    let cross_address_ok = pool == ActionPool::Ironwood;
    if flags & FLAGS_ALWAYS_UNSET != 0
        || (flags & FLAG_CROSS_ADDRESS_ENABLED != 0 && !cross_address_ok)
    {
        return Err(DecodeError::InvalidFlags {
            pool: pool.name(),
            flags,
        });
    }
    let value_balance = read_balance(
        r,
        match pool {
            ActionPool::Orchard => "Orchard value balance",
            ActionPool::Ironwood => "Ironwood value balance",
        },
    )?;
    let anchor = r.array("anchor")?;
    let proof = r.var_bytes("proof")?;
    if enforce_proof_size {
        // n is at most MAX_COMPACT_SIZE, so this cannot overflow on 64-bit
        // targets; checked arithmetic covers 32-bit ones.
        let expected = n
            .checked_mul(ACTION_PROOF_PER_ACTION_SIZE)
            .and_then(|v| v.checked_add(ACTION_PROOF_BASE_SIZE));
        if expected != Some(proof.len()) {
            return Err(DecodeError::InvalidProofLength {
                pool: pool.name(),
                expected: expected.unwrap_or(usize::MAX),
                actual: proof.len(),
            });
        }
    }
    for action in &mut actions {
        action.spend_auth_sig = r.array("action spendAuthSig")?;
    }
    Ok(Some(ActionBundle {
        pool,
        actions,
        flags,
        value_balance,
        anchor,
        proof,
        binding_sig: r.array("bindingSig")?,
    }))
}
