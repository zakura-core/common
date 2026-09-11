//! Observational captures of complete selected prover executions.
//!
//! This opt-in fixture API records the original RNG calls, public setup, synthesized
//! witness rows, transcript operations, challenges, and terminal result. It does not
//! replace any prover computation or establish equality of message distributions.
//! Captures contain the private witness and masks; use synthetic fixture inputs.
//!
//! Fixture drivers install the RNG and transcript wrappers explicitly. The prover
//! only exposes two read-only observation points for setup and synthesized rows;
//! those return immediately unless a capture scope is active.
//!
//! The `IZKCAP01` format starts with an eight-byte header. Each record contains a
//! one-byte tag, a little-endian `u32` payload length, and the payload. Dimensions
//! are little-endian `u32`s; Pasta field elements are canonical 32-byte little-endian
//! representatives. Points have an identity flag (`0`), or `1` followed by x and y.
//! RNG records preserve the method and returned bytes without resampling.

use std::{
    cell::RefCell,
    convert::Infallible,
    fmt,
    io::Write,
    rc::{Rc, Weak},
};

use ff::PrimeField;
use rand_core::{Rng, TryRng};

use crate::{
    arithmetic::{Coordinates, CurveAffine},
    poly::{LagrangeCoeff, Polynomial, commitment::Params},
    transcript::{Blake2bWrite, ChallengeScalar, EncodedChallenge, Transcript, TranscriptWrite},
};

mod vesta_lean;
pub use vesta_lean::dump_vesta_lean_prover_fixture;

/// Format identifier, including its version.
const HEADER: &[u8; 8] = b"IZKCAP01";
/// Both Pasta fields have canonical 256-bit encodings.
const FIELD_BYTES: usize = 32;

/// Stable wire tags distinguish RNG methods, transcript operations, and outcomes.
#[repr(u8)]
enum Tag {
    Setup = 1,
    Sigma = 2,
    Witness = 3,
    RngU32 = 10,
    RngU64 = 11,
    RngBytes = 12,
    CommonPoint = 20,
    CommonScalar = 21,
    WritePoint = 22,
    WriteScalar = 23,
    Challenge = 24,
    Success = 30,
    Error = 31,
    Panic = 32,
}

struct Capture {
    bytes: Vec<u8>,
    terminal: bool,
}

thread_local! {
    // Draws and transcript writes occur on the caller's thread. A weak reference
    // prevents abandoned guards from leaving capture enabled for unrelated calls.
    static CURRENT: RefCell<Weak<RefCell<Capture>>> = const { RefCell::new(Weak::new()) };
}

fn active() -> bool {
    CURRENT
        .try_with(|slot| slot.borrow().strong_count() != 0)
        .unwrap_or(false)
}

fn append(capture: &mut Capture, tag: Tag, payload: &[u8], terminal: bool) {
    assert!(
        !capture.terminal,
        "capture records exactly one completed proof call"
    );
    capture.bytes.push(tag as u8);
    capture.bytes.extend_from_slice(
        &u32::try_from(payload.len())
            .expect("fixture records fit in a u32 length")
            .to_le_bytes(),
    );
    capture.bytes.extend_from_slice(payload);
    capture.terminal = terminal;
}

fn emit(tag: Tag, payload: &[u8], terminal: bool) {
    // Another thread-local destructor can still use a wrapper after CURRENT is gone.
    let _ = CURRENT.try_with(|slot| {
        if let Some(capture) = slot.borrow().upgrade() {
            append(&mut capture.borrow_mut(), tag, payload, terminal);
        }
    });
}

/// A caller-thread capture scope for one proof call.
///
/// The `Rc` makes this guard non-`Send`: beginning, observing and finishing a
/// capture must occur on the same thread. Independent test threads can capture
/// independently. Nested captures are rejected.
pub struct ProverCapture {
    capture: Rc<RefCell<Capture>>,
}

impl fmt::Debug for ProverCapture {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProverCapture").finish_non_exhaustive()
    }
}

impl ProverCapture {
    /// Begin recording a proof whose RNG and transcript use the wrappers below.
    pub fn start() -> Self {
        let capture = Rc::new(RefCell::new(Capture {
            bytes: HEADER.to_vec(),
            terminal: false,
        }));
        CURRENT.with(|slot| {
            let mut current = slot.borrow_mut();
            assert!(
                current.upgrade().is_none(),
                "prover capture scopes cannot be nested"
            );
            *current = Rc::downgrade(&capture);
        });
        Self { capture }
    }

    /// Return the complete stream, requiring a recorded success, error, or panic.
    pub fn finish(self) -> Vec<u8> {
        let mut capture = self.capture.borrow_mut();
        assert!(
            capture.terminal,
            "a finished capture includes its terminal result"
        );
        std::mem::take(&mut capture.bytes)
    }
}

impl Drop for ProverCapture {
    fn drop(&mut self) {
        let _ = CURRENT.try_with(|slot| {
            *slot.borrow_mut() = Weak::new();
        });
    }
}

fn number(out: &mut Vec<u8>, value: usize) {
    out.extend_from_slice(
        &u32::try_from(value)
            .expect("fixture dimensions fit in a u32")
            .to_le_bytes(),
    );
}

fn field<F: PrimeField>(out: &mut Vec<u8>, value: &F) {
    let repr = value.to_repr();
    assert_eq!(repr.as_ref().len(), FIELD_BYTES, "Pasta field encoding");
    out.extend_from_slice(repr.as_ref());
}

fn point<C: CurveAffine>(out: &mut Vec<u8>, value: &C) {
    if let Some(coordinates) = Option::<Coordinates<C>>::from(value.coordinates()) {
        out.push(1);
        field(out, coordinates.x());
        field(out, coordinates.y());
    } else {
        out.push(0);
    }
}

fn matrix<F: PrimeField>(out: &mut Vec<u8>, columns: &[Polynomial<F, LagrangeCoeff>]) {
    number(out, columns.len());
    for column in columns {
        number(out, column.len());
        for value in column.iter() {
            field(out, value);
        }
    }
}

pub(super) fn record_setup<C: CurveAffine>(
    params: &Params<C>,
    pk: &super::ProvingKey<C>,
    instances: &[&[&[C::Scalar]]],
) {
    if !active() {
        return;
    }
    let mut out = Vec::new();
    number(&mut out, params.k as usize);
    number(&mut out, params.n as usize);
    number(&mut out, pk.vk.cs.blinding_factors());
    number(&mut out, pk.vk.cs.degree());
    number(&mut out, params.g.len());
    for generator in &params.g {
        point(&mut out, generator);
    }
    point(&mut out, &params.w);
    point(&mut out, &params.u);
    matrix(&mut out, &pk.fixed_values);
    number(&mut out, instances.len());
    for instance in instances {
        number(&mut out, instance.len());
        for column in *instance {
            number(&mut out, column.len());
            for value in *column {
                field(&mut out, value);
            }
        }
    }
    emit(Tag::Setup, &out, false);

    out.clear();
    matrix(&mut out, pk.permutation.permutations());
    emit(Tag::Sigma, &out, false);
}

pub(super) fn record_witness<F: PrimeField>(actions: &[Vec<Polynomial<F, LagrangeCoeff>>]) {
    if active() {
        let mut out = Vec::new();
        number(&mut out, actions.len());
        for columns in actions {
            matrix(&mut out, columns);
        }
        emit(Tag::Witness, &out, false);
    }
}

/// A pass-through RNG recording the method and every returned byte.
pub struct RecordingRng<R>(R);

impl<R> fmt::Debug for RecordingRng<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RecordingRng").finish_non_exhaustive()
    }
}

impl<R> RecordingRng<R> {
    /// Wrap the caller's RNG without drawing or reseeding it.
    pub fn new(inner: R) -> Self {
        Self(inner)
    }
}

impl<R: Rng> TryRng for RecordingRng<R> {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        let value = self.0.next_u32();
        emit(Tag::RngU32, &value.to_le_bytes(), false);
        Ok(value)
    }

    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        let value = self.0.next_u64();
        emit(Tag::RngU64, &value.to_le_bytes(), false);
        Ok(value)
    }

    fn try_fill_bytes(&mut self, output: &mut [u8]) -> Result<(), Infallible> {
        self.0.fill_bytes(output);
        emit(Tag::RngBytes, output, false);
        Ok(())
    }
}

/// A pass-through writer recording actual transcript inputs and outputs.
pub struct RecordingTranscript<T> {
    inner: Option<T>,
}

impl<T> fmt::Debug for RecordingTranscript<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RecordingTranscript")
            .finish_non_exhaustive()
    }
}

impl<T> RecordingTranscript<T> {
    /// Wrap the original transcript without absorbing or squeezing anything.
    pub fn new(inner: T) -> Self {
        Self { inner: Some(inner) }
    }
}

impl<W: Write, C: CurveAffine, E: EncodedChallenge<C>> RecordingTranscript<Blake2bWrite<W, C, E>> {
    /// Return the original proof buffer after recording successful completion.
    pub fn finalize(mut self) -> W {
        let output = self
            .inner
            .take()
            .expect("transcript has not been finalized")
            .finalize();
        emit(Tag::Success, &[], true);
        output
    }
}

impl<C: CurveAffine, E: EncodedChallenge<C>, T: Transcript<C, E>> Transcript<C, E>
    for RecordingTranscript<T>
{
    fn squeeze_challenge(&mut self) -> E {
        let challenge = self
            .inner
            .as_mut()
            .expect("transcript is live")
            .squeeze_challenge();
        if active() {
            let mut out = Vec::new();
            field(&mut out, &challenge.get_scalar());
            emit(Tag::Challenge, &out, false);
        }
        challenge
    }

    fn squeeze_challenge_scalar<Challenge>(&mut self) -> ChallengeScalar<C, Challenge> {
        // Preserve any typed-challenge override on the original transcript.
        let challenge = self
            .inner
            .as_mut()
            .expect("transcript is live")
            .squeeze_challenge_scalar::<Challenge>();
        if active() {
            let mut out = Vec::new();
            field(&mut out, &*challenge);
            emit(Tag::Challenge, &out, false);
        }
        challenge
    }

    fn common_point(&mut self, value: C) -> std::io::Result<()> {
        let result = self
            .inner
            .as_mut()
            .expect("transcript is live")
            .common_point(value);
        if active() {
            let mut out = vec![u8::from(result.is_ok())];
            point(&mut out, &value);
            emit(Tag::CommonPoint, &out, false);
        }
        result
    }

    fn common_scalar(&mut self, value: C::Scalar) -> std::io::Result<()> {
        let result = self
            .inner
            .as_mut()
            .expect("transcript is live")
            .common_scalar(value);
        if active() {
            let mut out = vec![u8::from(result.is_ok())];
            field(&mut out, &value);
            emit(Tag::CommonScalar, &out, false);
        }
        result
    }
}

impl<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>> TranscriptWrite<C, E>
    for RecordingTranscript<T>
{
    fn write_point(&mut self, value: C) -> std::io::Result<()> {
        let result = self
            .inner
            .as_mut()
            .expect("transcript is live")
            .write_point(value);
        if active() {
            let mut out = vec![u8::from(result.is_ok())];
            point(&mut out, &value);
            emit(Tag::WritePoint, &out, false);
        }
        result
    }

    fn write_scalar(&mut self, value: C::Scalar) -> std::io::Result<()> {
        let result = self
            .inner
            .as_mut()
            .expect("transcript is live")
            .write_scalar(value);
        if active() {
            let mut out = vec![u8::from(result.is_ok())];
            field(&mut out, &value);
            emit(Tag::WriteScalar, &out, false);
        }
        result
    }
}

/// Observe the exact error before the caller propagates it unchanged.
pub fn record_error(error: &super::Error) {
    if active() {
        emit(Tag::Error, format!("{error:?}").as_bytes(), true);
    }
}

impl<T> Drop for RecordingTranscript<T> {
    fn drop(&mut self) {
        if self.inner.is_some() && std::thread::panicking() {
            // Preserve the original panic, including when unwinding a recorder failure.
            let _ = CURRENT.try_with(|slot| {
                if let Ok(current) = slot.try_borrow()
                    && let Some(capture) = current.upgrade()
                    && let Ok(mut capture) = capture.try_borrow_mut()
                    && !capture.terminal
                {
                    append(&mut capture, Tag::Panic, &[], true);
                }
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        pasta::{EqAffine, Fp},
        transcript::Challenge255,
    };
    use group::CurveAffine as _;
    use proptest::prelude::*;
    use rand::{SeedableRng, rngs::StdRng};
    use rand_core::Rng;

    type TestTranscript = Blake2bWrite<Vec<u8>, EqAffine, Challenge255<EqAffine>>;

    /// A custom transcript that domain-separates typed challenge requests.
    struct TypedChallengeTranscript {
        inner: TestTranscript,
        domain_separator: Fp,
    }

    impl Transcript<EqAffine, Challenge255<EqAffine>> for TypedChallengeTranscript {
        fn squeeze_challenge(&mut self) -> Challenge255<EqAffine> {
            self.inner.squeeze_challenge()
        }

        fn squeeze_challenge_scalar<T>(&mut self) -> ChallengeScalar<EqAffine, T> {
            self.inner.common_scalar(self.domain_separator).unwrap();
            self.inner.squeeze_challenge_scalar()
        }

        fn common_point(&mut self, point: EqAffine) -> std::io::Result<()> {
            self.inner.common_point(point)
        }

        fn common_scalar(&mut self, scalar: Fp) -> std::io::Result<()> {
            self.inner.common_scalar(scalar)
        }
    }

    fn records(bytes: &[u8]) -> Vec<(u8, Vec<u8>)> {
        assert_eq!(&bytes[..HEADER.len()], HEADER);
        let mut bytes = &bytes[HEADER.len()..];
        let mut result = Vec::new();
        while !bytes.is_empty() {
            let tag = bytes[0];
            let length = u32::from_le_bytes(bytes[1..5].try_into().unwrap()) as usize;
            result.push((tag, bytes[5..5 + length].to_vec()));
            bytes = &bytes[5 + length..];
        }
        result
    }

    proptest! {
        #[test]
        fn rng_methods_and_bytes_are_unchanged(seed: u64, methods in prop::collection::vec(0u8..3, 1..40)) {
            let mut original = StdRng::seed_from_u64(seed);
            let mut wrapped = RecordingRng::new(StdRng::seed_from_u64(seed));
            let capture = ProverCapture::start();
            let mut expected = Vec::new();
            for method in methods {
                match method {
                    0 => {
                        let value = original.next_u32();
                        prop_assert_eq!(wrapped.next_u32(), value);
                        expected.push((Tag::RngU32 as u8, value.to_le_bytes().to_vec()));
                    }
                    1 => {
                        let value = original.next_u64();
                        prop_assert_eq!(wrapped.next_u64(), value);
                        expected.push((Tag::RngU64 as u8, value.to_le_bytes().to_vec()));
                    }
                    _ => {
                        // A non-word length exercises the RNG's original partial-word policy.
                        let mut a = [0u8; 13];
                        let mut b = [0u8; 13];
                        original.fill_bytes(&mut a);
                        wrapped.fill_bytes(&mut b);
                        prop_assert_eq!(a, b);
                        expected.push((Tag::RngBytes as u8, a.to_vec()));
                    }
                }
            }
            let next = original.next_u64();
            prop_assert_eq!(wrapped.next_u64(), next);
            expected.push((Tag::RngU64 as u8, next.to_le_bytes().to_vec()));
            emit(Tag::Success, &[], true);
            expected.push((Tag::Success as u8, Vec::new()));
            prop_assert_eq!(records(&capture.finish()), expected);
        }

        #[test]
        fn transcript_messages_and_challenges_are_unchanged(value: u64) {
            let capture = ProverCapture::start();
            let mut original = TestTranscript::init(Vec::new());
            let mut wrapped = RecordingTranscript::new(TestTranscript::init(Vec::new()));
            let scalar = Fp::from(value);
            let point = EqAffine::generator();
            original.common_scalar(scalar).unwrap();
            wrapped.common_scalar(scalar).unwrap();
            original.common_point(point).unwrap();
            wrapped.common_point(point).unwrap();
            original.write_scalar(scalar).unwrap();
            wrapped.write_scalar(scalar).unwrap();
            original.write_point(point).unwrap();
            wrapped.write_point(point).unwrap();
            prop_assert_eq!(original.squeeze_challenge().get_scalar(), wrapped.squeeze_challenge().get_scalar());
            prop_assert_eq!(original.finalize(), wrapped.finalize());
            let captured = records(&capture.finish());
            prop_assert_eq!(captured.iter().map(|r| r.0).collect::<Vec<_>>(), vec![
                Tag::CommonScalar as u8, Tag::CommonPoint as u8, Tag::WriteScalar as u8,
                Tag::WritePoint as u8, Tag::Challenge as u8, Tag::Success as u8,
            ]);
            let mut expected_scalar = vec![1];
            field(&mut expected_scalar, &scalar);
            let mut expected_point = vec![1];
            super::point(&mut expected_point, &point);
            prop_assert_eq!(&captured[0].1, &expected_scalar);
            prop_assert_eq!(&captured[1].1, &expected_point);
            prop_assert_eq!(&captured[2].1, &expected_scalar);
            prop_assert_eq!(&captured[3].1, &expected_point);
        }

        #[test]
        fn typed_challenge_overrides_are_preserved(domain_separator: u64) {
            for recording in [false, true] {
                let capture = recording.then(ProverCapture::start);
                let make_transcript = || TypedChallengeTranscript {
                    inner: TestTranscript::init(Vec::new()),
                    domain_separator: Fp::from(domain_separator),
                };
                let mut original = make_transcript();
                let mut wrapped = RecordingTranscript::new(make_transcript());

                let typed = *original.squeeze_challenge_scalar::<()>();
                prop_assert_eq!(*wrapped.squeeze_challenge_scalar::<()>(), typed);
                // A subsequent squeeze also observes any state changes in the override.
                let encoded = original.squeeze_challenge().get_scalar();
                prop_assert_eq!(wrapped.squeeze_challenge().get_scalar(), encoded);

                if let Some(capture) = capture {
                    emit(Tag::Success, &[], true);
                    prop_assert_eq!(records(&capture.finish()), vec![
                        (Tag::Challenge as u8, typed.to_repr().to_vec()),
                        (Tag::Challenge as u8, encoded.to_repr().to_vec()),
                        (Tag::Success as u8, Vec::new()),
                    ]);
                }
            }
        }
    }

    #[test]
    fn identity_rejection_preserves_the_original_error() {
        let capture = ProverCapture::start();
        let mut original = TestTranscript::init(Vec::new());
        let mut wrapped = RecordingTranscript::new(TestTranscript::init(Vec::new()));
        let expected = original.write_point(EqAffine::identity()).unwrap_err();
        let error = wrapped.write_point(EqAffine::identity()).unwrap_err();
        assert_eq!(error.kind(), expected.kind());
        assert_eq!(error.to_string(), expected.to_string());
        record_error(&crate::plonk::Error::Transcript(error));
        let captured = records(&capture.finish());
        assert_eq!(captured[0], (Tag::WritePoint as u8, vec![0, 0]));
        assert_eq!(captured[1].0, Tag::Error as u8);
        assert!(captured[1].1.starts_with(b"Transcript("));
    }

    #[test]
    fn unwinding_records_panic_without_intercepting_it() {
        let capture = ProverCapture::start();
        let result = std::panic::catch_unwind(|| {
            let _transcript = RecordingTranscript::new(TestTranscript::init(Vec::new()));
            panic!("fixture panic sentinel");
        });
        assert_eq!(
            *result.unwrap_err().downcast::<&str>().unwrap(),
            "fixture panic sentinel"
        );
        assert_eq!(records(&capture.finish()), vec![(Tag::Panic as u8, vec![])]);
    }

    #[test]
    fn incomplete_captures_are_rejected_and_scopes_are_released() {
        assert!(std::panic::catch_unwind(|| ProverCapture::start().finish()).is_err());
        let capture = ProverCapture::start();
        record_error(&crate::plonk::Error::Opening);
        assert_eq!(
            records(&capture.finish()),
            vec![(Tag::Error as u8, b"Opening".to_vec())]
        );
        assert!(!active());
    }

    #[test]
    fn inactive_wrappers_survive_thread_local_destruction() {
        struct OnDrop(std::sync::mpsc::Sender<std::thread::Result<()>>);

        impl Drop for OnDrop {
            fn drop(&mut self) {
                // Catch failures here so a destructor panic does not abort the test process.
                let result = std::panic::catch_unwind(|| {
                    let mut original = StdRng::seed_from_u64(0);
                    let mut wrapped = RecordingRng::new(StdRng::seed_from_u64(0));
                    assert_eq!(wrapped.next_u32(), original.next_u32());
                    assert_eq!(wrapped.next_u64(), original.next_u64());
                    let mut expected = [0; 13];
                    let mut actual = [0; 13];
                    original.fill_bytes(&mut expected);
                    wrapped.fill_bytes(&mut actual);
                    assert_eq!(actual, expected);

                    assert!(!active());
                    let mut original = TestTranscript::init(Vec::new());
                    let mut wrapped = RecordingTranscript::new(TestTranscript::init(Vec::new()));
                    let scalar = Fp::from(7);
                    original.common_scalar(scalar).unwrap();
                    wrapped.common_scalar(scalar).unwrap();
                    original.write_scalar(scalar).unwrap();
                    wrapped.write_scalar(scalar).unwrap();
                    assert_eq!(
                        original.squeeze_challenge().get_scalar(),
                        wrapped.squeeze_challenge().get_scalar()
                    );
                    assert_eq!(original.finalize(), wrapped.finalize());
                });
                let _ = self.0.send(result);
            }
        }

        thread_local! {
            static ON_DROP: RefCell<Option<OnDrop>> = const { RefCell::new(None) };
        }

        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            ON_DROP.with(|slot| *slot.borrow_mut() = Some(OnDrop(sender)));
            // Initialize the recorder second so its TLS is destroyed before ON_DROP.
            assert!(!active());
        })
        .join()
        .unwrap();
        assert!(
            receiver.recv().unwrap().is_ok(),
            "inactive wrappers must preserve operations during thread-local destruction"
        );
    }

    #[test]
    fn simultaneous_captures_are_isolated_by_caller_thread() {
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
        let handles: Vec<_> = (0..2)
            .map(|index| {
                let barrier = barrier.clone();
                std::thread::spawn(move || {
                    let capture = ProverCapture::start();
                    barrier.wait();
                    emit(Tag::RngU32, &u32::to_le_bytes(index), false);
                    emit(Tag::Success, &[], true);
                    assert_eq!(
                        records(&capture.finish()),
                        vec![
                            (Tag::RngU32 as u8, index.to_le_bytes().to_vec()),
                            (Tag::Success as u8, Vec::new()),
                        ]
                    );
                })
            })
            .collect();
        for handle in handles {
            handle.join().unwrap();
        }
        assert!(!active());
    }
}
