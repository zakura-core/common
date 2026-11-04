//! Public request records and their canonical encoding boundary.
//!
//! Field and point wrappers retain validated native arithmetic values. The private
//! `NativeStatement` gives witness construction, preflight, proving, and verification
//! one shared interpretation of the public-input slots. The proving pipeline checks
//! witness relations, while verification checks the supplied proof.

use crate::public_input;

use crate::Error;
use udon::field::Fp as NativeFp;

#[cfg(all(test, feature = "prover"))]
pub(crate) use crate::test_codec::{ACTION_SIZE, HEADER_SIZE};

#[cfg(all(test, feature = "prover"))]
use crate::primitives::ENCODED_VALUE_SIZE;
pub(crate) use crate::primitives::Fp;
#[cfg(feature = "prover")]
pub(crate) use crate::primitives::{Fq, NonIdentityPallasPoint, PallasPoint, SpendValidatingKey};

/// Number of siblings in an Ironwood note-commitment authentication path: the
/// circuit's fixed tree depth.
#[cfg(feature = "prover")]
pub(crate) use sensei_shared::MERKLE_DEPTH;

/// Public values for one Orchard or Ironwood Action.
#[derive(Clone)]
pub struct PublicStatement {
    /// The note-commitment tree anchor against which the spend is proven.
    ///
    /// When the spent value `v_old` is nonzero, this must equal the root
    /// computed from the spent note commitment and its authentication path.
    /// A zero spent value permits any anchor, but witness construction still
    /// evaluates the full path.
    pub anchor: Fp,
    /// The affine `(x, y)` coordinates of the net value commitment.
    ///
    /// Must lie on Pallas, or be `(0, 0)` to denote the identity.
    pub cv_net: (Fp, Fp),
    /// The nullifier of the note being spent.
    ///
    /// Also supplies the new note's rho value; the private witness has no
    /// separate `rho_new` field.
    pub nf_old: Fp,
    /// The affine `(x, y)` coordinates of the randomized spend validating key.
    ///
    /// Must be a non-identity Pallas point; `(0, 0)` is rejected.
    pub rk: (Fp, Fp),
    /// The extracted commitment to the note being created.
    pub cmx: Fp,
    /// Whether the spend is enabled.
    ///
    /// When false, the spent value `v_old` must be zero. When true, `v_old`
    /// may still be zero. Witness construction and constraint checks run for
    /// the spend in either case.
    pub enable_spend: bool,
    /// Whether the output is enabled.
    ///
    /// When false, the new note's value `v_new` must be zero. When true,
    /// `v_new` may still be zero. Witness construction and constraint checks
    /// run for the output in either case.
    pub enable_output: bool,
    /// Whether the proof must enforce the cross-address restriction.
    ///
    /// When true, the old and new recipient pairs `(g_d_old, pk_d_old)` and
    /// `(g_d_new, pk_d_new)` must match, even when both note values are zero.
    pub disable_cross_address: bool,
}

/// Private witness values for one Ironwood Action.
#[derive(Clone)]
#[cfg(feature = "prover")]
pub struct PrivateWitness {
    /// Siblings in the spent note's authentication path, ordered from leaf
    /// to root.
    ///
    /// At layer `i`, bit `i` of [`Self::position`] (least significant bit
    /// first) orders the current node and `path[i]`: zero places the current
    /// node on the left, and one places it on the right.
    pub path: [Fp; MERKLE_DEPTH],
    /// The spent note commitment's position in its tree.
    ///
    /// Its bits select the ordering described by [`Self::path`].
    pub position: u32,
    /// The diversified base of the spent note's recipient.
    pub g_d_old: NonIdentityPallasPoint,
    /// The diversified transmission key of the spent note's recipient.
    pub pk_d_old: NonIdentityPallasPoint,
    /// The value of the spent note.
    pub v_old: u64,
    /// The spent note's rho value.
    pub rho_old: Fp,
    /// The spent note's psi value.
    pub psi_old: Fp,
    /// The spent note commitment trapdoor.
    pub rcm_old: Fq,
    /// The spent note commitment.
    pub cm_old: PallasPoint,
    /// The randomizer for the spend validating key.
    pub alpha: Fq,
    /// The spend validating key.
    pub ak: SpendValidatingKey,
    /// The nullifier deriving key.
    pub nk: Fp,
    /// The randomness for the incoming viewing-key commitment.
    pub rivk: Fq,
    /// The diversified base of the new note's recipient.
    pub g_d_new: NonIdentityPallasPoint,
    /// The diversified transmission key of the new note's recipient.
    pub pk_d_new: NonIdentityPallasPoint,
    /// The value of the new note.
    pub v_new: u64,
    /// The new note's psi value.
    pub psi_new: Fp,
    /// The new note commitment trapdoor.
    pub rcm_new: Fq,
    /// The net value commitment trapdoor.
    pub rcv: Fq,
}

/// One public statement and its private witness.
#[derive(Clone)]
#[cfg(feature = "prover")]
pub struct Action {
    /// The public values to be proven.
    pub statement: PublicStatement,
    /// The private values that establish the statement.
    pub witness: PrivateWitness,
}

/// An owned collection of Ironwood Actions to prove together.
///
/// Accepts any nonempty collection whose proof and work dimensions fit the
/// implementation's slice and index representations. Memory demand grows with
/// the Action count; representability does not guarantee an allocation can
/// succeed. Callers enforce their own resource limits before constructing a
/// request.
#[cfg(feature = "prover")]
pub struct ProvingRequest {
    actions: Vec<Action>,
    pub(crate) shape: crate::sizing::RequestShape,
}

#[cfg(feature = "prover")]
impl ProvingRequest {
    /// Creates a proving request from a nonempty collection of Actions.
    ///
    /// Returns [`Error::InvalidInput`] if the collection is empty, its storage
    /// dimensions are unrepresentable, or a public point is invalid.
    /// Takes ownership of the Actions, dropping them on error.
    ///
    /// Field and point wrappers check canonical encodings when decoding; this
    /// constructor checks request shape and public-point validity.
    /// [`crate::create_proof`] checks statement/witness relations and circuit
    /// satisfaction. Request construction consumes no randomness and does not
    /// prepare proving tables.
    pub fn new(actions: Vec<Action>) -> Result<Self, Error> {
        let shape = crate::sizing::RequestShape::new(actions.len())?;
        if actions
            .iter()
            .any(|action| !action.statement.valid_points())
        {
            return Err(Error::InvalidInput);
        }
        Ok(Self { actions, shape })
    }

    pub(crate) fn actions(&self) -> &[Action] {
        &self.actions
    }

    pub(crate) fn action_count(&self) -> usize {
        self.shape.actions
    }

    /// Each Action's populated instance prefix (`public_input::COUNT`
    /// values), from the shared native statement record.
    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn instance_columns(&self) -> Vec<Vec<NativeFp>> {
        self.actions
            .iter()
            .map(|action| action.statement.native().to_vec())
            .collect()
    }

    /// Every Action's circuit-native statement record, decoded once for the
    /// whole proof and owned by the pipeline: the witness writer, preflight,
    /// and the prover's initialization read these records instead of each
    /// decoding the public statement on its own.
    pub(crate) fn native_statements(&self) -> Vec<NativeStatement> {
        self.actions
            .iter()
            .map(|action| action.statement.native())
            .collect()
    }

    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn decode_iwpr_for_test(bytes: &[u8]) -> Result<Self, Error> {
        crate::test_codec::decode_iwpr(bytes)
    }
}

/// One Action's public statement in circuit-native form: the instance
/// column's populated prefix, indexed by the circuit's named public-input
/// slots (`public_input::*`). The private view every native consumer reads —
/// the witness writer's top-level relations, preflight's instance column,
/// the prover's instance polynomials, and the verifier's public inputs — instead
/// of each decoding the public bytes on its own terms.
///
/// **Established by the public constructors** (and therefore by this record's
/// construction, which cannot fail): every `Fp` carries a canonical field
/// encoding, so each slot is a valid field element, and the flags are the
/// field's zero or one. **Not established here:** the relations between these
/// values and the witness — the nullifier and commitment derivations, the
/// anchor as a Merkle root, the spend/output enable semantics — which the
/// witness writer's top-level relation checks and preflight's constraint
/// checks verify.
#[derive(Clone, Copy)]
pub(crate) struct NativeStatement([NativeFp; public_input::COUNT]);

impl NativeStatement {
    /// The prefix as an `N`-row instance column: the named slots followed by
    /// zeros, in one allocation.
    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn instance_column(&self, rows: usize) -> Vec<NativeFp> {
        let mut column = Vec::with_capacity(rows);
        column.extend_from_slice(&self.0);
        column.resize(rows, NativeFp::ZERO);
        column
    }
}

impl std::ops::Deref for NativeStatement {
    type Target = [NativeFp; public_input::COUNT];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PublicStatement {
    fn valid_points(&self) -> bool {
        valid_affine_point(self.cv_net.0, self.cv_net.1, true)
            && valid_affine_point(self.rk.0, self.rk.1, false)
    }

    /// The statement's circuit-native record; see [`NativeStatement`].
    pub(crate) fn native(&self) -> NativeStatement {
        let native = Fp::native;
        let mut values = [NativeFp::ZERO; public_input::COUNT];
        values[public_input::ANCHOR] = native(self.anchor);
        values[public_input::CV_NET_X] = native(self.cv_net.0);
        values[public_input::CV_NET_Y] = native(self.cv_net.1);
        values[public_input::NF_OLD] = native(self.nf_old);
        values[public_input::RK_X] = native(self.rk.0);
        values[public_input::RK_Y] = native(self.rk.1);
        values[public_input::CMX] = native(self.cmx);
        values[public_input::ENABLE_SPEND] = NativeFp::from_u64(self.enable_spend.into());
        values[public_input::ENABLE_OUTPUT] = NativeFp::from_u64(self.enable_output.into());
        values[public_input::DISABLE_CROSS_ADDRESS] =
            NativeFp::from_u64(self.disable_cross_address.into());
        NativeStatement(values)
    }

    /// The native prefix as a vector; the test scaffolding's convenience over
    /// [`Self::native`].
    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn native_values(&self) -> Vec<NativeFp> {
        self.native().to_vec()
    }
}

fn valid_affine_point(x: Fp, y: Fp, allow_identity: bool) -> bool {
    if x.is_zero() && y.is_zero() {
        return allow_identity;
    }
    udon::curve::PallasAffine::from_xy(x.native().reduce(), y.native().reduce()).is_some()
}

/// The pinned Orchard Action circuit against which a proof is verified.
///
/// The caller selects the version required by its protocol context. Proof
/// creation through `crate::create_proof` uses [`Self::PostNu6_3`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CircuitVersion {
    /// The current circuit, including the cross-address restriction.
    PostNu6_3,
    /// The fixed circuit used between NU6.2 and NU6.3, for historical verification.
    FixedPostNu6_2,
    /// The original circuit with unanchored variable-base multiplication,
    /// retained for verification of history before NU6.2.
    InsecurePreNu6_2,
}

impl CircuitVersion {
    #[cfg(feature = "verifier")]
    pub(crate) const fn index(self) -> usize {
        match self {
            Self::PostNu6_3 => 0,
            Self::FixedPostNu6_2 => 1,
            Self::InsecurePreNu6_2 => 2,
        }
    }

    #[cfg(feature = "verifier")]
    pub(crate) const fn instance_len(self) -> usize {
        match self {
            Self::PostNu6_3 => public_input::COUNT,
            Self::FixedPostNu6_2 | Self::InsecurePreNu6_2 => public_input::DISABLE_CROSS_ADDRESS,
        }
    }

    #[cfg(feature = "verifier")]
    pub(crate) fn vk_representative(self) -> NativeFp {
        match self {
            Self::PostNu6_3 => crate::native::protocol::vk_representative(),
            Self::FixedPostNu6_2 => {
                udon::fp_hex!("0x0bf7d48f59be0bbef33c558826dffee0032deccb9a6d2ea23daf3812d32d5271")
            }
            Self::InsecurePreNu6_2 => {
                udon::fp_hex!("0x1530570202d7575b7d4da2e5f524da02dfcad69185bacc99cdfa1ec1706d0819")
            }
        }
    }
}

/// A borrowed proof, its circuit version, and its ordered Action statements.
///
/// Verification has no Action-count ceiling. The statements must be nonempty
/// and the proof must have the canonical length for that many Actions, except
/// that pre-NU6.2 proofs may contain an ignored trailing suffix.
#[derive(Clone, Copy)]
#[cfg(feature = "verifier")]
pub struct VerificationRequest<'a> {
    pub(crate) version: CircuitVersion,
    pub(crate) statements: &'a [PublicStatement],
    pub(crate) proof: &'a [u8],
}
#[cfg(feature = "verifier")]
impl<'a> VerificationRequest<'a> {
    /// Validates the request's shape and public points without copying it.
    ///
    /// Returns [`Error::InvalidInput`] for empty statements, invalid points,
    /// an unrepresentable proof size, a truncated proof, a noncanonical proof
    /// length for NU6.2 or later, or [`PublicStatement::disable_cross_address`]
    /// set to true for either circuit version before NU6.3. Proof contents are
    /// checked by [`crate::verify_proofs`].
    pub fn new(
        version: CircuitVersion,
        statements: &'a [PublicStatement],
        proof: &'a [u8],
    ) -> Result<Self, Error> {
        let expected =
            crate::native::protocol::transcript_encoding::proof_capacity(statements.len())
                .ok_or(Error::InvalidInput)?;
        if statements.is_empty()
            || proof.len() < expected
            || (version != CircuitVersion::InsecurePreNu6_2 && proof.len() != expected)
            || statements.iter().any(|s| {
                !s.valid_points()
                    || (version != CircuitVersion::PostNu6_3 && s.disable_cross_address)
            })
        {
            return Err(Error::InvalidInput);
        }
        Ok(Self {
            version,
            statements,
            // Historical Halo2 verification consumed only the transcript's
            // expected prefix. Keep that rule without copying or changing the
            // caller's wire bytes (which also enter bundle authorization hashes).
            proof: &proof[..expected],
        })
    }
}

#[cfg(all(test, feature = "prover"))]
mod tests {
    use super::{ENCODED_VALUE_SIZE, Error, Fp, Fq, ProvingRequest};

    use crate::Fr;

    /// The Pallas base-field modulus `p`, little-endian, transcribed
    /// independently of every arithmetic constant in the workspace.
    const P_BYTES: [u8; ENCODED_VALUE_SIZE] = [
        0x01, 0x00, 0x00, 0x00, 0xed, 0x30, 0x2d, 0x99, 0x1b, 0xf9, 0x4c, 0x09, 0xfc, 0x98, 0x46,
        0x22, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x40,
    ];
    /// The Pallas scalar-field modulus `q`, likewise independent.
    const Q_BYTES: [u8; ENCODED_VALUE_SIZE] = [
        0x01, 0x00, 0x00, 0x00, 0x21, 0xeb, 0x46, 0x8c, 0xdd, 0xa8, 0x94, 0x09, 0xfc, 0x98, 0x46,
        0x22, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x40,
    ];

    /// The canonical boundary of both public field types, pinned against the
    /// independent literals: the modulus and anything above are rejected,
    /// the modulus minus one is accepted. (Both moduli end in `…01`, so the
    /// predecessor is the same encoding with a zero low byte.)
    #[test]
    fn public_field_encodings_are_canonical_below_their_moduli() {
        fn check(modulus: [u8; ENCODED_VALUE_SIZE], decode: fn([u8; ENCODED_VALUE_SIZE]) -> bool) {
            assert!(decode([0; ENCODED_VALUE_SIZE]));
            let mut below = modulus;
            below[0] = 0x00;
            assert!(decode(below));
            assert!(!decode(modulus));
            let mut above = modulus;
            above[0] = 0x02;
            assert!(!decode(above));
            assert!(!decode([0xff; ENCODED_VALUE_SIZE]));
        }
        check(P_BYTES, |bytes| Fp::from_bytes(bytes).is_ok());
        check(Q_BYTES, |bytes| Fq::from_bytes(bytes).is_ok());
        // The two moduli differ (`p < q`), and each constructor knows which
        // is its own: `p` is a canonical scalar but `q` is not a canonical
        // base-field element.
        assert!(Fq::from_bytes(P_BYTES).is_ok());
        assert!(matches!(Fp::from_bytes(Q_BYTES), Err(Error::InvalidInput)));
    }

    #[test]
    fn public_scalar_field_uses_fq_modulus_and_preserves_fr_alias() {
        let zero = Fq::from_bytes([0; ENCODED_VALUE_SIZE]).unwrap();
        let compatibility_value: Fr = zero;
        let _: Fq = compatibility_value;
        assert!(matches!(Fq::from_bytes(Q_BYTES), Err(Error::InvalidInput)));
    }

    #[test]
    fn request_accepts_dynamic_nonempty_action_sets() {
        assert_eq!(
            ProvingRequest::new(Vec::new()).err(),
            Some(Error::InvalidInput)
        );

        let request =
            ProvingRequest::decode_iwpr_for_test(crate::test_codec::FIXTURES[0].request).unwrap();
        let actions = (0..128)
            .map(|_| {
                let request =
                    ProvingRequest::decode_iwpr_for_test(crate::test_codec::FIXTURES[0].request)
                        .unwrap();
                request.actions()[0].clone()
            })
            .collect();
        assert_eq!(ProvingRequest::new(actions).unwrap().action_count(), 128);
        assert_eq!(request.action_count(), 1);
    }
}
