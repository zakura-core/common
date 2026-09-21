#![cfg(feature = "unstable-prover-fingerprint")]

use std::{
    fmt,
    io::{self, Write},
    sync::Arc,
};

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    pasta::{EqAffine, Fp},
    plonk::{
        self, Advice, Circuit, Column, ConstraintSystem, Error, Instance, ProvingKey,
        SingleVerifier,
        prover_fingerprint::{ProverCapture, RecordingRng, RecordingTranscript, record_error},
    },
    poly::commitment::Params,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255, Transcript, TranscriptWrite},
};
use rand::{Rng, SeedableRng, rngs::StdRng};

const WITNESS: u64 = 7;
const SEED: u64 = 0x415;

#[derive(Clone)]
struct SmallCircuit;

impl Circuit<Fp> for SmallCircuit {
    type Config = (Column<Advice>, Column<Instance>);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let advice = meta.advice_column();
        let instance = meta.instance_column();
        meta.enable_equality(advice);
        meta.enable_equality(instance);
        (advice, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let cell = layouter.assign_region(
            || "witness",
            |mut region| {
                region.assign_advice(|| "value", config.0, 0, || Value::known(Fp::from(WITNESS)))
            },
        )?;
        layouter.constrain_instance(cell.cell(), config.1, 0)
    }
}

fn keys() -> (Params<EqAffine>, ProvingKey<EqAffine>) {
    let params = Params::new(4);
    let vk = plonk::keygen_vk(&params, &SmallCircuit).unwrap();
    let pk = plonk::keygen_pk(&params, vk, &SmallCircuit).unwrap();
    (params, pk)
}

fn prove<T: TranscriptWrite<EqAffine, Challenge255<EqAffine>>>(
    params: &Params<EqAffine>,
    pk: &ProvingKey<EqAffine>,
    transcript: &mut T,
    rng: impl Rng,
) -> Result<(), Error> {
    plonk::create_proof(
        params,
        pk,
        &[SmallCircuit],
        &[&[&[Fp::from(WITNESS)]]],
        rng,
        transcript,
    )
}

/// A transcript outside the recorder's specialized Blake2b finalization API.
struct CustomTranscript(Blake2bWrite<Vec<u8>, EqAffine, Challenge255<EqAffine>>);

impl Transcript<EqAffine, Challenge255<EqAffine>> for CustomTranscript {
    fn squeeze_challenge(&mut self) -> Challenge255<EqAffine> {
        self.0.squeeze_challenge()
    }

    fn common_point(&mut self, point: EqAffine) -> io::Result<()> {
        self.0.common_point(point)
    }

    fn common_scalar(&mut self, scalar: Fp) -> io::Result<()> {
        self.0.common_scalar(scalar)
    }
}

impl TranscriptWrite<EqAffine, Challenge255<EqAffine>> for CustomTranscript {
    fn write_point(&mut self, point: EqAffine) -> io::Result<()> {
        self.0.write_point(point)
    }

    fn write_scalar(&mut self, scalar: Fp) -> io::Result<()> {
        self.0.write_scalar(scalar)
    }
}

#[test]
fn custom_transcript_success_can_finish_capture() {
    let (params, pk) = keys();
    let mut original = CustomTranscript(Blake2bWrite::init(Vec::new()));
    prove(&params, &pk, &mut original, StdRng::seed_from_u64(SEED)).unwrap();
    let expected = original.0.finalize();

    for recording in [false, true] {
        let capture = recording.then(ProverCapture::start);
        let mut transcript =
            RecordingTranscript::new(CustomTranscript(Blake2bWrite::init(Vec::new())));
        prove(
            &params,
            &pk,
            &mut transcript,
            RecordingRng::new(StdRng::seed_from_u64(SEED)),
        )
        .unwrap();

        let proof = transcript.finish().0.finalize();
        assert_eq!(proof, expected);
        plonk::verify_proof(
            &params,
            pk.get_vk(),
            SingleVerifier::new(&params),
            &[&[&[Fp::from(WITNESS)]]],
            &mut Blake2bRead::init(&proof[..]),
        )
        .unwrap();
        if let Some(capture) = capture {
            // The Success record has tag 30 and an empty payload.
            assert!(capture.finish().ends_with(&[30, 0, 0, 0, 0]));
        }
    }
}

struct UnformattableError(Arc<()>);

impl fmt::Debug for UnformattableError {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("the recorder must not call custom Debug")
    }
}

impl fmt::Display for UnformattableError {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("the recorder must not call custom Display")
    }
}

impl std::error::Error for UnformattableError {}

struct FailingWriter(Arc<()>);

impl Write for FailingWriter {
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::Error::other(UnformattableError(Arc::clone(&self.0))))
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn assert_original_error(result: Result<(), Error>, identity: &Arc<()>) {
    let Err(Error::Transcript(error)) = result else {
        panic!("expected the writer's transcript error");
    };
    assert_eq!(error.kind(), io::ErrorKind::Other);
    let original = error
        .get_ref()
        .unwrap()
        .downcast_ref::<UnformattableError>()
        .unwrap();
    assert!(Arc::ptr_eq(&original.0, identity));
}

#[test]
fn recording_preserves_unformattable_transcript_errors() {
    let (params, pk) = keys();
    let identity = Arc::new(());
    assert_original_error(
        prove(
            &params,
            &pk,
            &mut Blake2bWrite::init(FailingWriter(Arc::clone(&identity))),
            StdRng::seed_from_u64(SEED),
        ),
        &identity,
    );

    for recording in [false, true] {
        let capture = recording.then(ProverCapture::start);
        let mut transcript =
            RecordingTranscript::new(Blake2bWrite::init(FailingWriter(Arc::clone(&identity))));
        let result = prove(
            &params,
            &pk,
            &mut transcript,
            RecordingRng::new(StdRng::seed_from_u64(SEED)),
        )
        .inspect_err(record_error);
        assert_original_error(result, &identity);
        drop(transcript);
        if let Some(capture) = capture {
            // The Error record has tag 31 and only the built-in error kind.
            assert!(
                capture
                    .finish()
                    .ends_with(b"\x1f\x11\x00\x00\x00Transcript(Other)")
            );
        }
    }
}
