//! Private fixture codec and prepared resources for unit tests.
//!
//! This module is compiled only for unit tests. It owns the fixture container's
//! selectors and sizes; none are a production request or proof format. The
//! public-API golden harness maintains its own independent decoder, so changing
//! this scaffolding cannot redefine the proof oracle.
//! See the [oracle-independence map](crate::native#oracle-independence) for the
//! boundary between fixture decoding, shared arithmetic, and frozen expectations.
//!
//! The fixture corpus lives in `fixtures`, IWPR decoding and tape replay in
//! `codec`, and shared target preparation in `prepared`.

mod codec;
mod fixtures;
mod prepared;

pub(crate) use codec::{ACTION_SIZE, HEADER_SIZE, TapeRng, decode_iwpr};
pub(crate) use fixtures::{FIXTURES, Fixture};
pub(crate) use prepared::{execution, target};

mod tests {
    use super::{HEADER_SIZE, decode_iwpr};
    use crate::Error;

    const FIXTURE: &[u8] = include_bytes!("../tests/fixtures/one-action.iwpr");

    #[test]
    fn codec_is_strict_and_test_only() {
        assert_eq!(decode_iwpr(FIXTURE).unwrap().action_count(), 1);
        assert_eq!(
            decode_iwpr(&FIXTURE[..HEADER_SIZE]).err(),
            Some(Error::InvalidInput)
        );

        let mut trailing = FIXTURE.to_vec();
        trailing.push(0);
        assert_eq!(decode_iwpr(&trailing).err(), Some(Error::InvalidInput));

        let mut wrong_target = FIXTURE.to_vec();
        wrong_target[8] ^= 1;
        assert_eq!(decode_iwpr(&wrong_target).err(), Some(Error::InvalidInput));
    }
}
