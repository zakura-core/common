//! Compatibility with the `zcash_encoding` 0.4.0 wire format.

use corez::io::{self, Read, Write};
use zcash_protocol::encoding::{Array, CompactSize, MAX_COMPACT_SIZE, Optional, Vector};

#[test]
fn compact_size_canonical_boundaries() {
    for (value, bytes) in [
        (0, &[0][..]),
        (252, &[252][..]),
        (253, &[253, 253, 0][..]),
        (u16::MAX as usize, &[253, 255, 255][..]),
        (u16::MAX as usize + 1, &[254, 0, 0, 1, 0][..]),
        (MAX_COMPACT_SIZE as usize, &[254, 0, 0, 0, 2][..]),
    ] {
        let mut encoded = Vec::new();
        CompactSize::write(&mut encoded, value).unwrap();
        assert_eq!(encoded, bytes);
        assert_eq!(CompactSize::serialized_size(value), bytes.len());
        assert_eq!(CompactSize::read(bytes).unwrap(), value as u64);
    }
}

#[test]
fn compact_size_rejects_noncanonical_and_oversized_inputs() {
    for (bytes, message) in [
        (&[253, 0, 0][..], "non-canonical CompactSize"),
        (&[253, 252, 0][..], "non-canonical CompactSize"),
        (&[254, 253, 0, 0, 0][..], "non-canonical CompactSize"),
        (&[254, 255, 255, 0, 0][..], "non-canonical CompactSize"),
        (
            &[255, 0, 0, 1, 0, 0, 0, 0, 0][..],
            "non-canonical CompactSize",
        ),
        (
            &[255, 255, 255, 255, 255, 0, 0, 0, 0][..],
            "non-canonical CompactSize",
        ),
        (&[254, 1, 0, 0, 2][..], "CompactSize too large"),
        (&[255, 0, 0, 0, 0, 1, 0, 0, 0][..], "CompactSize too large"),
    ] {
        let error = CompactSize::read(bytes).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
        assert_eq!(error.to_string(), message);
    }
    let error = CompactSize::read_t::<_, u8>(&[253, 0, 1][..]).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
}

#[test]
fn compact_size_rejects_every_truncated_prefix() {
    for bytes in [
        &[0][..],
        &[253, 253, 0][..],
        &[254, 0, 0, 1, 0][..],
        &[255, 0, 0, 0, 0, 1, 0, 0, 0][..],
    ] {
        for length in 0..bytes.len() {
            assert_eq!(
                CompactSize::read(&bytes[..length]).unwrap_err().kind(),
                io::ErrorKind::UnexpectedEof,
            );
        }
    }
}

#[test]
fn compact_size_writer_preserves_unbounded_0_4_behavior() {
    let mut cases = vec![
        (MAX_COMPACT_SIZE as usize + 1, vec![254, 1, 0, 0, 2]),
        (u32::MAX as usize, vec![254, 255, 255, 255, 255]),
    ];
    // The nine-byte writer branch is reachable only on 64-bit targets.
    #[cfg(target_pointer_width = "64")]
    cases.extend([
        (u32::MAX as usize + 1, vec![255, 0, 0, 0, 0, 1, 0, 0, 0]),
        (
            usize::MAX,
            vec![255, 255, 255, 255, 255, 255, 255, 255, 255],
        ),
    ]);
    for (value, expected) in cases {
        let mut encoded = Vec::new();
        CompactSize::write(&mut encoded, value).unwrap();
        assert_eq!(encoded, expected);
        assert_eq!(CompactSize::serialized_size(value), expected.len());
        assert_eq!(
            CompactSize::read(&encoded[..]).unwrap_err().kind(),
            io::ErrorKind::InvalidInput,
        );
    }
}

#[test]
fn compact_size_writer_preserves_partial_write_errors() {
    let mut storage = [0; 2];
    let error = CompactSize::write(&mut storage[..], 253).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::WriteZero);
    // corez uses std's slice writer with std enabled; its no_std slice
    // writer rejects the incomplete payload before copying any of it.
    // Both behaviors match the corresponding upstream 0.4.0 features.
    #[cfg(feature = "std")]
    assert_eq!(storage, [253, 253]);
    #[cfg(not(feature = "std"))]
    assert_eq!(storage, [253, 0]);
}

fn read_byte<R: Read>(reader: &mut R) -> io::Result<u8> {
    let mut byte = [0];
    reader.read_exact(&mut byte)?;
    Ok(byte[0])
}

#[test]
fn collection_and_optional_error_boundaries() {
    // An invalid length must fail before attempting to decode an element.
    assert_eq!(
        Vector::read(&[253, 0, 0][..], |_| -> io::Result<u8> {
            panic!("invalid prefix")
        })
        .unwrap_err()
        .kind(),
        io::ErrorKind::InvalidInput,
    );
    assert_eq!(
        Vector::read(&[2, 42][..], read_byte).unwrap_err().kind(),
        io::ErrorKind::UnexpectedEof,
    );
    assert_eq!(
        Array::read(&[42][..], 2, read_byte).unwrap_err().kind(),
        io::ErrorKind::UnexpectedEof,
    );
    for flag in 2..=u8::MAX {
        assert_eq!(
            Optional::read(&[flag][..], |_| -> io::Result<u8> {
                panic!("invalid flag")
            })
            .unwrap_err()
            .kind(),
            io::ErrorKind::InvalidInput,
        );
    }
    assert_eq!(
        Optional::read(&[][..], read_byte_owned).unwrap_err().kind(),
        io::ErrorKind::UnexpectedEof,
    );
    assert_eq!(
        Optional::read(&[1][..], read_byte_owned)
            .unwrap_err()
            .kind(),
        io::ErrorKind::UnexpectedEof,
    );
}

fn read_byte_owned<R: Read>(mut reader: R) -> io::Result<u8> {
    read_byte(&mut reader)
}

#[test]
fn collected_and_nonempty_encodings_match_vectors() {
    let values = nonempty::NonEmpty {
        head: 42,
        tail: vec![43],
    };
    let mut encoded = Vec::new();
    Vector::write_nonempty(&mut encoded, &values, |w, b| w.write_all(&[*b])).unwrap();
    assert_eq!(encoded, [2, 42, 43]);
    let mut calls = 0;
    let collected: Vec<_> = Vector::read_collected_mut(&encoded[..], |r| {
        calls += 1;
        read_byte(r)
    })
    .unwrap();
    assert_eq!(collected, [42, 43]);
    assert_eq!(calls, values.len());
}

/// A reader over `data` that returns at most `step` bytes per call, reports
/// `Interrupted` once at `interrupt_at`, and fails at `fail_at`.
struct ScriptedReader<'a> {
    data: &'a [u8],
    position: usize,
    step: usize,
    interrupt_at: Option<usize>,
    fail_at: Option<usize>,
    calls: usize,
    largest_request: usize,
}

impl<'a> ScriptedReader<'a> {
    fn new(data: &'a [u8], step: usize) -> Self {
        Self {
            data,
            position: 0,
            step,
            interrupt_at: None,
            fail_at: None,
            calls: 0,
            largest_request: 0,
        }
    }
}

impl Read for ScriptedReader<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.calls += 1;
        self.largest_request = self.largest_request.max(buf.len());
        if self.interrupt_at == Some(self.position) {
            self.interrupt_at = None;
            return Err(io::Error::new(io::ErrorKind::Interrupted, "interrupted"));
        }
        if self.fail_at == Some(self.position) {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "reader failed"));
        }
        let mut end = self
            .data
            .len()
            .min(self.position + self.step.min(buf.len()));
        for stop in [self.interrupt_at, self.fail_at].into_iter().flatten() {
            if stop > self.position {
                end = end.min(stop);
            }
        }
        let read = end - self.position;
        buf[..read].copy_from_slice(&self.data[self.position..end]);
        self.position = end;
        Ok(read)
    }
}

fn outcome(result: io::Result<Vec<u8>>) -> Result<Vec<u8>, (io::ErrorKind, String)> {
    result.map_err(|error| (error.kind(), error.to_string()))
}

proptest::proptest! {
    /// `read_bytes` returns the same bytes and errors as the per-byte decoder,
    /// and leaves the same input unread.
    #[test]
    fn read_bytes_matches_per_byte_decoding(
        declared in proptest::prop_oneof![
            0usize..=10_000,
            proptest::prelude::Just(MAX_COMPACT_SIZE as usize),
        ],
        available in 0usize..=10_000,
        trailing in 0usize..=4,
        step in 1usize..=5_000,
        interrupt_at in proptest::option::of(0usize..=10_010),
        fail_at in proptest::option::of(0usize..=10_010),
    ) {
        let mut data = Vec::new();
        CompactSize::write(&mut data, declared).unwrap();
        let prefix = data.len();
        data.extend((0..available.min(declared) + trailing).map(|i| i as u8));

        let reader = |data| {
            let mut reader = ScriptedReader::new(data, step);
            reader.interrupt_at = interrupt_at;
            reader.fail_at = fail_at;
            reader
        };
        let mut expected_reader = reader(&data);
        let expected = outcome(Vector::read(&mut expected_reader, read_byte));
        let mut actual_reader = reader(&data);
        let actual = outcome(Vector::read_bytes(&mut actual_reader));
        proptest::prop_assert_eq!(&actual, &expected);
        proptest::prop_assert_eq!(actual_reader.position, expected_reader.position);

        let mut expected_reader = reader(&data[prefix..]);
        let expected = outcome(Array::read(&mut expected_reader, declared, read_byte));
        let mut actual_reader = reader(&data[prefix..]);
        let actual = outcome(Array::read_bytes(&mut actual_reader, declared));
        proptest::prop_assert_eq!(&actual, &expected);
        proptest::prop_assert_eq!(actual_reader.position, expected_reader.position);
    }
}

#[test]
fn read_bytes_rejects_invalid_lengths_before_reading_contents() {
    for bytes in [
        &[253, 0, 0][..],
        &[254, 255, 255, 0, 0][..],
        &[254, 1, 0, 0, 2][..],
    ] {
        let mut reader = ScriptedReader::new(bytes, usize::MAX);
        let error = Vector::read_bytes(&mut reader).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
        assert_eq!(reader.position, bytes.len());
    }
}

#[test]
fn read_bytes_reads_in_bounded_chunks() {
    let mut data = Vec::new();
    Vector::write(&mut data, &[7; 10_000], |w, b| w.write_all(&[*b])).unwrap();
    let mut reader = ScriptedReader::new(&data, usize::MAX);
    assert_eq!(Vector::read_bytes(&mut reader).unwrap(), [7; 10_000]);
    // Two reads for the length prefix, then three chunks for the contents.
    assert_eq!(reader.calls, 5);
    assert_eq!(reader.largest_request, 4096);

    // A large declared length on short input requests one chunk, not the
    // declared length, before failing.
    let mut data = Vec::new();
    CompactSize::write(&mut data, MAX_COMPACT_SIZE as usize).unwrap();
    data.extend([7; 100]);
    let mut reader = ScriptedReader::new(&data, usize::MAX);
    assert_eq!(
        Vector::read_bytes(&mut reader).unwrap_err().kind(),
        io::ErrorKind::UnexpectedEof,
    );
    assert_eq!(reader.largest_request, 4096);
}
