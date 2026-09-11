//! Lean source export for the recorded successful Orchard prover profiles.

use std::{fmt::Write as _, io};

use ff::PrimeField;

use super::{FIELD_BYTES, HEADER, Tag};
use crate::{
    arithmetic::CurveAffine,
    pasta::{EqAffine, Fp, Fq},
};

/// The released Orchard fixture circuit has 2^11 rows.
const K: usize = 11;
const ROWS: usize = 1 << K;
/// These are the fixed, permutation, and advice column counts of PostNu6_3.
const FIXED: usize = 29;
const SIGMA: usize = 15;
const ADVICE: usize = 10;
/// Each Action has one public instance column containing ten values before padding.
const INSTANCE_VALUES: usize = 10;
/// The successful fixture profile has five blinded rows and degree nine.
const BLINDING: usize = 5;
const DEGREE: usize = 9;
/// A two-Action execution is smaller than this bound, including its synthesized rows.
const MAX_BYTES: usize = 8_000_000;

fn require(condition: bool, message: &'static str) -> io::Result<()> {
    if condition {
        Ok(())
    } else {
        Err(io::Error::new(io::ErrorKind::InvalidData, message))
    }
}

/// Hexadecimal Nat literals preserve the canonical little-endian bytes exactly.
fn natural(bytes: &[u8]) -> String {
    let mut hex = String::new();
    for byte in bytes.iter().rev() {
        write!(hex, "{byte:02x}").unwrap();
    }
    let digits = hex.trim_start_matches('0');
    if digits.is_empty() {
        "0".into()
    } else {
        format!("0x{digits}")
    }
}

fn array(values: &[String]) -> String {
    format!("#[{}]", values.join(", "))
}

fn lean_namespace(namespace: &str) -> io::Result<String> {
    require(
        namespace.split('.').all(|part| {
            !part.is_empty()
                && part.as_bytes()[0].is_ascii_alphabetic()
                && part
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        }),
        "invalid Lean namespace",
    )?;
    // Quoting each component preserves the name even when a component is a Lean keyword.
    Ok(namespace
        .split('.')
        .map(|part| format!("«{part}»"))
        .collect::<Vec<_>>()
        .join("."))
}

struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    fn take(&mut self, size: usize) -> io::Result<&'a [u8]> {
        require(size <= self.0.len(), "truncated prover capture")?;
        let (value, rest) = self.0.split_at(size);
        self.0 = rest;
        Ok(value)
    }

    fn number(&mut self) -> io::Result<usize> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()) as usize)
    }

    fn dimension(&mut self, expected: usize) -> io::Result<()> {
        let actual = self.number()?;
        require(actual == expected, "unsupported prover fixture dimension")
    }

    fn record(&mut self) -> io::Result<(u8, Reader<'a>)> {
        let tag = self.take(1)?[0];
        let length = self.number()?;
        Ok((tag, Reader(self.take(length)?)))
    }

    fn required(&mut self, expected: Tag) -> io::Result<Reader<'a>> {
        let (tag, payload) = self.record()?;
        require(tag == expected as u8, "unexpected prover capture record")?;
        Ok(payload)
    }

    fn field<F: PrimeField>(&mut self) -> io::Result<(F, String)> {
        let bytes = self.take(FIELD_BYTES)?;
        let mut repr = F::Repr::default();
        repr.as_mut().copy_from_slice(bytes);
        let value = Option::<F>::from(F::from_repr(repr)).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "noncanonical field encoding")
        })?;
        Ok((value, natural(bytes)))
    }

    fn point(&mut self, identity_allowed: bool) -> io::Result<String> {
        match self.take(1)?[0] {
            0 => {
                require(identity_allowed, "identity in a successful transcript")?;
                Ok(".identity".into())
            }
            1 => {
                let (x, x_text) = self.field::<Fq>()?;
                let (y, y_text) = self.field::<Fq>()?;
                // Pasta accepts (0, 0) as identity, which must use the separate wire tag.
                require(
                    bool::from(
                        EqAffine::from_xy(x, y)
                            .and_then(|point| point.coordinates())
                            .is_some(),
                    ),
                    "point is not on Vesta",
                )?;
                Ok(format!("(.affine {x_text} {y_text})"))
            }
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid point tag",
            )),
        }
    }

    fn successful(&mut self) -> io::Result<()> {
        require(self.take(1)? == [1], "failed transcript operation")
    }

    fn fields(&mut self, count: usize) -> io::Result<Vec<String>> {
        self.dimension(count)?;
        (0..count)
            .map(|_| self.field::<Fp>().map(|(_, text)| text))
            .collect()
    }

    fn matrix(&mut self, columns: usize) -> io::Result<Vec<Vec<String>>> {
        self.dimension(columns)?;
        (0..columns).map(|_| self.fields(ROWS)).collect()
    }

    fn end(self) -> io::Result<()> {
        require(self.0.is_empty(), "trailing prover capture payload")
    }
}

fn columns(out: &mut String, prefix: &str, rows: &[Vec<String>]) -> String {
    let mut names = Vec::new();
    for (index, column) in rows.iter().enumerate() {
        let name = format!("{prefix}{index}");
        writeln!(
            out,
            "/-- Column {index} of the captured {prefix} rows, in domain order. -/"
        )
        .unwrap();
        writeln!(out, "def {name} : Array Nat := {}\n", array(column)).unwrap();
        names.push(name);
    }
    array(&names)
}

/// Export a complete successful Vesta prover capture as an importable Lean fixture.
///
/// The accepted profiles are the one- and two-Action PostNu6_3 Orchard drivers.
/// The emitted data includes public setup, pre-mask witness rows, every original
/// u64 RNG draw, ordered transcript operations, and terminal success. Ironwood's
/// independent decoder validates the data before replaying the prover. `proof`
/// must be the original proof buffer from the same call; it is exported unchanged
/// alongside the recorded messages as a separate comparison target.
/// Namespace components are quoted so that Lean keywords remain identifiers.
///
/// Returns an error for malformed or unsupported captures and invalid namespaces.
pub fn dump_vesta_lean_prover_fixture(
    namespace: &str,
    bytes: &[u8],
    proof: &[u8],
) -> io::Result<String> {
    let namespace = lean_namespace(namespace)?;
    require(
        bytes.len() <= MAX_BYTES,
        "prover capture exceeds supported capacity",
    )?;
    let mut stream = Reader(bytes);
    require(
        stream.take(HEADER.len())? == HEADER,
        "unsupported capture version",
    )?;
    let mut initial = stream.required(Tag::CommonScalar)?;
    initial.successful()?;
    let mut initialization = vec![format!(".scalar {}", initial.field::<Fp>()?.1)];
    initial.end()?;

    let mut setup = stream.required(Tag::Setup)?;
    for expected in [K, ROWS, BLINDING, DEGREE, ROWS] {
        setup.dimension(expected)?;
    }
    let generators = (0..ROWS)
        .map(|_| setup.point(true))
        .collect::<io::Result<Vec<_>>>()?;
    let w = setup.point(true)?;
    let u = setup.point(true)?;
    let fixed = setup.matrix(FIXED)?;
    let actions = setup.number()?;
    require(matches!(actions, 1 | 2), "unsupported Action count")?;
    let mut instances = Vec::new();
    for _ in 0..actions {
        setup.dimension(1)?;
        instances.push(array(&setup.fields(INSTANCE_VALUES)?));
    }
    setup.end()?;
    let mut permutation = stream.required(Tag::Sigma)?;
    let sigma = permutation.matrix(SIGMA)?;
    permutation.end()?;
    for _ in 0..actions {
        let mut point = stream.required(Tag::CommonPoint)?;
        point.successful()?;
        initialization.push(format!(".point {}", point.point(false)?));
        point.end()?;
    }
    let mut advice = stream.required(Tag::Witness)?;
    advice.dimension(actions)?;
    let witness = (0..actions)
        .map(|_| advice.matrix(ADVICE))
        .collect::<io::Result<Vec<_>>>()?;
    advice.end()?;

    let mut events = Vec::new();
    let mut counts = [0usize; 4]; // RNG words, points, scalars, challenges.
    let mut boundaries = Vec::new();
    loop {
        let (tag, mut payload) = stream.record()?;
        let event = match tag {
            tag if tag == Tag::RngU64 as u8 => {
                counts[0] += 1;
                format!(".rng64 {}", natural(payload.take(8)?))
            }
            tag if tag == Tag::WritePoint as u8 => {
                counts[1] += 1;
                payload.successful()?;
                format!(".point {}", payload.point(false)?)
            }
            tag if tag == Tag::WriteScalar as u8 => {
                counts[2] += 1;
                payload.successful()?;
                format!(".scalar {}", payload.field::<Fp>()?.1)
            }
            tag if tag == Tag::Challenge as u8 => {
                counts[3] += 1;
                boundaries.push(counts[0]);
                format!(".challenge {}", payload.field::<Fp>()?.1)
            }
            tag if tag == Tag::Success as u8 => {
                payload.end()?;
                stream.end()?;
                events.push(".success".into());
                break;
            }
            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "unsupported prover operation",
                ));
            }
        };
        payload.end()?;
        events.push(event);
    }
    require(
        counts
            == [
                8 * (148 * actions + 46),
                22 * actions + 33,
                49 * actions + 52,
                22,
            ],
        "incomplete prover operation inventory",
    )?;
    let mut expected = vec![
        70 * actions,
        112 * actions,
        112 * actions,
        148 * actions + 3,
        148 * actions + 11,
        148 * actions + 11,
        148 * actions + 11,
        148 * actions + 12,
        148 * actions + 12,
        148 * actions + 24,
        148 * actions + 24,
    ];
    expected.extend((0..K).map(|round| 148 * actions + 26 + 2 * round));
    require(
        boundaries == expected.iter().map(|count| 8 * count).collect::<Vec<_>>(),
        "RNG stage boundaries changed",
    )?;
    require(
        proof.len() == FIELD_BYTES * (counts[1] + counts[2]),
        "proof buffer has the wrong length",
    )?;

    let mut out = String::from(
        "-- Auto-generated by halo2 `dump_vesta_lean_prover_fixture`. Do not edit by hand.\n",
    );
    // Match the verifier exporter's recursion setting for its long data literals.
    writeln!(out, "import Zcash.Snark.Fixtures.Prover.FixtureData\n\nset_option maxRecDepth 1000000\n\nnamespace {namespace}\n\nopen Zcash.Snark.Fixtures.Prover\n").unwrap();
    writeln!(out, "/-- Monomial-basis commitment generators recorded by Rust. -/\ndef capturedGenerators : Array FixturePoint := {}\n", array(&generators)).unwrap();
    let fixed = columns(&mut out, "fixed", &fixed);
    let sigma = columns(&mut out, "sigma", &sigma);
    let witness = witness
        .iter()
        .enumerate()
        .map(|(action, rows)| columns(&mut out, &format!("witness{action}Column"), rows))
        .collect::<Vec<_>>();
    writeln!(out, "/-- Every RNG draw, proof message, challenge, and terminal result, in call order. -/\ndef capturedEvents : Array FixtureEvent := {}\n", array(&events)).unwrap();
    writeln!(out, "/-- Original Rust proof buffer, independent of the exported message encodings. -/\ndef capturedProof : Array Nat := {}\n", array(&proof.iter().map(u8::to_string).collect::<Vec<_>>())).unwrap();
    writeln!(out, "/-- Complete selected Rust prover execution, with outputs separate from synthesized rows. -/\ndef captured : ProverFixture := {{\n  setup := {{\n    k := {K}\n    rows := {ROWS}\n    blindingFactors := {BLINDING}\n    degree := {DEGREE}\n    generators := capturedGenerators\n    w := {w}\n    u := {u}\n    fixed := {fixed}\n    sigma := {sigma} }}\n  instances := {}\n  witness := {}\n  initialization := {}\n  events := capturedEvents\n  proof := capturedProof\n}}\n\nend {namespace}", array(&instances), array(&witness), array(&initialization)).unwrap();
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_capture_and_namespace_are_rejected() {
        for namespace in [
            "",
            "Fixture; axiom injected : False",
            "Fixture..Case",
            "1Fixture",
            "Fixture.«match»",
        ] {
            assert_eq!(
                dump_vesta_lean_prover_fixture(namespace, HEADER, &[])
                    .unwrap_err()
                    .to_string(),
                "invalid Lean namespace"
            );
        }
        for bytes in [b"".as_slice(), HEADER.as_slice(), b"IZKCAP02".as_slice()] {
            assert!(dump_vesta_lean_prover_fixture("Fixture", bytes, &[]).is_err());
        }
    }

    #[test]
    fn reserved_namespace_components_are_quoted() {
        assert_eq!(lean_namespace("match").unwrap(), "«match»");
        assert_eq!(
            lean_namespace("Fixture_2.match.end").unwrap(),
            "«Fixture_2».«match».«end»"
        );
    }

    #[test]
    fn affine_identity_encoding_is_rejected() {
        let mut affine_identity = [0; 1 + 2 * FIELD_BYTES];
        affine_identity[0] = 1;
        for identity_allowed in [false, true] {
            assert!(Reader(&affine_identity).point(identity_allowed).is_err());
        }
        // Identity has its own wire tag and is permitted only in the setup.
        assert_eq!(Reader(&[0]).point(true).unwrap(), ".identity");
        assert!(Reader(&[0]).point(false).is_err());
    }

    #[test]
    fn canonical_words_retain_their_endianness() {
        assert_eq!(natural(&[0, 0]), "0");
        assert_eq!(natural(&[0x12, 0x34, 0, 0]), "0x3412");
        let mut bytes = [0; FIELD_BYTES];
        bytes[0] = 1;
        assert_eq!(Reader(&bytes).field::<Fp>().unwrap().1, "0x1");
        assert!(Reader(&[u8::MAX; FIELD_BYTES]).field::<Fp>().is_err());
    }
}
