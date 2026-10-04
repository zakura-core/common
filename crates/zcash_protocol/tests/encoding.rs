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
