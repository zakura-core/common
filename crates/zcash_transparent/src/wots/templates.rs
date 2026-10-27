//! The account redeem script and the control output.

use ripemd::Ripemd160;
use sha2::{Digest, Sha256};

use super::{OP_CHECKWOTSACCOUNT, OP_WOTSCONTROL, VERSION};
use crate::address::{Script, TransparentAddress};

/// The P2SH redeem script that defines an account: its version and the step-0 key-set root.
///
/// Encoded as `0x01 v 0x20 K(0) OP_CHECKWOTSACCOUNT`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AccountScript {
    /// Must be [`VERSION`] for a spend to be valid.
    pub version: u8,
    /// The key-set root of step 0.
    pub root: [u8; 32],
}

impl AccountScript {
    /// Encoded size in bytes.
    pub const SIZE: usize = 36;

    /// A current-version account committing to the step-0 key-set root.
    pub fn new(root: [u8; 32]) -> Self {
        Self {
            version: VERSION,
            root,
        }
    }

    /// Recognizes the template with any version byte; consensus rejects unknown versions.
    pub fn parse(bytes: &[u8]) -> Option<Self> {
        let bytes: &[u8; Self::SIZE] = bytes.try_into().ok()?;
        (bytes[0] == 1 && bytes[2] == 32 && bytes[35] == OP_CHECKWOTSACCOUNT).then(|| Self {
            version: bytes[1],
            root: bytes[3..35].try_into().expect("fixed slice"),
        })
    }

    /// The redeem script bytes.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut bytes = [0; Self::SIZE];
        bytes[0] = 1;
        bytes[1] = self.version;
        bytes[2] = 32;
        bytes[3..35].copy_from_slice(&self.root);
        bytes[35] = OP_CHECKWOTSACCOUNT;
        bytes
    }

    /// The account hash `A`, which is the P2SH script hash.
    pub fn account_hash(&self) -> [u8; 20] {
        Ripemd160::digest(Sha256::digest(self.to_bytes())).into()
    }

    /// The account's ordinary P2SH address.
    pub fn address(&self) -> TransparentAddress {
        TransparentAddress::ScriptHash(self.account_hash())
    }
}

/// The output naming the key-set root allowed to sign an account's next spend.
///
/// Encoded as `0x01 v 0x14 A 0x20 K(n) 0x04 n OP_WOTSCONTROL`, with `n` little-endian.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ControlOutput {
    /// Must be [`VERSION`] for a spend or creation to be valid.
    pub version: u8,
    /// The account hash `A` this output controls.
    pub account: [u8; 20],
    /// The key-set root of step `step`.
    pub root: [u8; 32],
    /// The number of spends the account has made.
    pub step: u32,
}

impl ControlOutput {
    /// Encoded size in bytes.
    pub const SIZE: usize = 62;

    /// A current-version control output.
    pub fn new(account: [u8; 20], root: [u8; 32], step: u32) -> Self {
        Self {
            version: VERSION,
            account,
            root,
            step,
        }
    }

    /// Recognizes the template with any version byte; consensus rejects unknown versions.
    pub fn parse(bytes: &[u8]) -> Option<Self> {
        let bytes: &[u8; Self::SIZE] = bytes.try_into().ok()?;
        (bytes[0] == 1
            && bytes[2] == 20
            && bytes[23] == 32
            && bytes[56] == 4
            && bytes[61] == OP_WOTSCONTROL)
            .then(|| Self {
                version: bytes[1],
                account: bytes[3..23].try_into().expect("fixed slice"),
                root: bytes[24..56].try_into().expect("fixed slice"),
                step: u32::from_le_bytes(bytes[57..61].try_into().expect("fixed slice")),
            })
    }

    /// The output script bytes.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut bytes = [0; Self::SIZE];
        bytes[0] = 1;
        bytes[1] = self.version;
        bytes[2] = 20;
        bytes[3..23].copy_from_slice(&self.account);
        bytes[23] = 32;
        bytes[24..56].copy_from_slice(&self.root);
        bytes[56] = 4;
        bytes[57..61].copy_from_slice(&self.step.to_le_bytes());
        bytes[61] = OP_WOTSCONTROL;
        bytes
    }

    /// The output script.
    pub fn script(&self) -> Script {
        Script(zcash_script::script::Code(self.to_bytes().to_vec()))
    }
}
