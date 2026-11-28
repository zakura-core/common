//! The ZIP 248 coinbase bundle.

use alloc::vec::Vec;
use core::fmt;
use corez::io::{self, Read, Write};

use blake2b_simd::Hash as Blake2bHash;
use zcash_protocol::{
    consensus::BlockHeight,
    encoding::{CompactSize, Vector},
    value::Zatoshis,
};

use super::digest::hasher;
use crate::encoding::{ReadBytesExt, WriteBytesExt};

/// T.3.1 `coinbase_effects_digest`.
const COINBASE_PERSONALIZATION: &[u8; 16] = b"ZTxIdCoinbasHash";

/// The maximum length of `coinbaseData`.
pub const MAX_COINBASE_DATA_LEN: usize = 94;

/// A miner's signal on one subject of a poll.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MinerSignal {
    /// The subject of the signal.
    pub signal_code: u8,
    /// The miner's level of support for the subject.
    pub level_of_support: u8,
}

/// The signals a miner gives in response to one poll.
///
/// Consensus assigns no meaning to the signals beyond their encoding rules; the Miner
/// Sentiment Polling draft ZIP specifies their use.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinerPoll {
    signals: Vec<MinerSignal>,
    poll_digest: [u8; 16],
}

impl MinerPoll {
    /// Constructs a poll response from signals in strictly ascending order of
    /// `signal_code`, which implies there are at most 256.
    pub fn new(signals: Vec<MinerSignal>, poll_digest: [u8; 16]) -> Result<Self, CoinbaseError> {
        if signals.is_empty() {
            return Err(CoinbaseError::EmptyMinerPoll);
        }
        if signals
            .windows(2)
            .any(|pair| pair[1].signal_code <= pair[0].signal_code)
        {
            return Err(CoinbaseError::UnorderedMinerSignals);
        }
        Ok(Self {
            signals,
            poll_digest,
        })
    }

    /// Returns the signals, in ascending order of `signal_code`.
    pub fn signals(&self) -> &[MinerSignal] {
        &self.signals
    }

    /// Returns the digest identifying the poll that the signals respond to.
    pub fn poll_digest(&self) -> &[u8; 16] {
        &self.poll_digest
    }
}

/// A violation of the coinbase bundle's encoding or bundle-local rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CoinbaseError {
    /// `blockHeight` is not in `{1 .. 499999999}`.
    BlockHeightOutOfRange,
    /// `lockboxValue` is greater than `blockSubsidy`.
    LockboxExceedsSubsidy,
    /// `coinbaseData` is longer than [`MAX_COINBASE_DATA_LEN`] bytes.
    CoinbaseDataTooLong,
    /// The signals are not in strictly ascending order of `signal_code`.
    UnorderedMinerSignals,
    /// A poll response has no signals; it is encoded by omitting the poll instead.
    EmptyMinerPoll,
}

impl fmt::Display for CoinbaseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BlockHeightOutOfRange => write!(f, "coinbase blockHeight is out of range"),
            Self::LockboxExceedsSubsidy => {
                write!(f, "coinbase lockboxValue exceeds its blockSubsidy")
            }
            Self::CoinbaseDataTooLong => write!(
                f,
                "coinbaseData is longer than {MAX_COINBASE_DATA_LEN} bytes"
            ),
            Self::UnorderedMinerSignals => {
                write!(f, "miner signals are not in strictly ascending order")
            }
            Self::EmptyMinerPoll => write!(f, "a miner poll response needs at least one signal"),
        }
    }
}

impl core::error::Error for CoinbaseError {}

/// The effecting data of a coinbase bundle, whose presence makes a v7 transaction a
/// coinbase transaction.
///
/// It replaces the coinbase input of earlier transaction versions, and carries the block
/// height that input encoded. A coinbase bundle has no authorizing data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoinbaseBundle {
    block_height: BlockHeight,
    block_subsidy: Zatoshis,
    lockbox_value: Zatoshis,
    coinbase_data: Vec<u8>,
    miner_poll: Option<MinerPoll>,
}

impl CoinbaseBundle {
    /// Constructs a coinbase bundle, checking the ZIP 248 rules on its fields.
    ///
    /// Whether the fields match the block that contains the transaction is checked by
    /// consensus, not here.
    pub fn new(
        block_height: BlockHeight,
        block_subsidy: Zatoshis,
        lockbox_value: Zatoshis,
        coinbase_data: Vec<u8>,
        miner_poll: Option<MinerPoll>,
    ) -> Result<Self, CoinbaseError> {
        if !(1..=super::MAX_V7_HEIGHT).contains(&u32::from(block_height)) {
            return Err(CoinbaseError::BlockHeightOutOfRange);
        }
        if lockbox_value > block_subsidy {
            return Err(CoinbaseError::LockboxExceedsSubsidy);
        }
        if coinbase_data.len() > MAX_COINBASE_DATA_LEN {
            return Err(CoinbaseError::CoinbaseDataTooLong);
        }
        Ok(Self {
            block_height,
            block_subsidy,
            lockbox_value,
            coinbase_data,
            miner_poll,
        })
    }

    /// Returns the height of the block in which the transaction is mined.
    pub fn block_height(&self) -> BlockHeight {
        self.block_height
    }

    /// Returns the block subsidy for that block.
    pub fn block_subsidy(&self) -> Zatoshis {
        self.block_subsidy
    }

    /// Returns the part of the block subsidy deposited into the lockbox.
    pub fn lockbox_value(&self) -> Zatoshis {
        self.lockbox_value
    }

    /// Returns the data chosen by the miner.
    pub fn coinbase_data(&self) -> &[u8] {
        &self.coinbase_data
    }

    /// Returns the miner's response to a poll, if any.
    pub fn miner_poll(&self) -> Option<&MinerPoll> {
        self.miner_poll.as_ref()
    }

    /// Reads the coinbase effecting data.
    pub(crate) fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let block_height = BlockHeight::from_u32(reader.read_u32_le()?);
        let block_subsidy = read_zatoshis(&mut reader)?;
        let lockbox_value = read_zatoshis(&mut reader)?;
        let coinbase_data = Vector::read_bytes(&mut reader)?;
        let signals = Vector::read(&mut reader, |r| {
            let mut signal = [0; 2];
            r.read_exact(&mut signal)?;
            Ok(MinerSignal {
                signal_code: signal[0],
                level_of_support: signal[1],
            })
        })?;
        let miner_poll = if signals.is_empty() {
            None
        } else {
            let mut poll_digest = [0; 16];
            reader.read_exact(&mut poll_digest)?;
            Some(MinerPoll::new(signals, poll_digest).map_err(invalid)?)
        };
        Self::new(
            block_height,
            block_subsidy,
            lockbox_value,
            coinbase_data,
            miner_poll,
        )
        .map_err(invalid)
    }

    /// Writes the coinbase effecting data.
    pub(crate) fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_u32_le(self.block_height.into())?;
        writer.write_u64_le(self.block_subsidy.into_u64())?;
        writer.write_u64_le(self.lockbox_value.into_u64())?;
        Vector::write(&mut writer, &self.coinbase_data, |w, b| w.write_all(&[*b]))?;
        match &self.miner_poll {
            None => CompactSize::write(&mut writer, 0),
            Some(poll) => {
                Vector::write(&mut writer, &poll.signals, |w, s| {
                    w.write_all(&[s.signal_code, s.level_of_support])
                })?;
                writer.write_all(&poll.poll_digest)
            }
        }
    }

    /// T.3.1: `coinbase_effects_digest`, which hashes the fields in their encoding.
    pub(crate) fn effects_digest(&self) -> Blake2bHash {
        let mut h = hasher(COINBASE_PERSONALIZATION);
        self.write(&mut h)
            .expect("writing to a hash state cannot fail");
        h.finalize()
    }
}

fn read_zatoshis<R: Read>(mut reader: R) -> io::Result<Zatoshis> {
    Zatoshis::from_u64(reader.read_u64_le()?)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "coinbase value is out of range"))
}

fn invalid(error: CoinbaseError) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, error)
}
