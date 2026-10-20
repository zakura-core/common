//! A real external caller: only public Orchard imports, no payment circuit internals.
use orchard::{
    circuit::voting::*,
    keys::{Diversifier, FullViewingKey, Scope, SpendValidatingKey, testing::arb_spending_key},
    note::{Note, NoteVersion, RandomSeed, Rho},
    value::NoteValue,
};
use orchard_legacy::halo2_gadgets::{
    ecc::{
        CircuitVersion, NonIdentityPoint, ScalarFixed, ScalarVar,
        chip::{EccChip, EccConfig},
    },
    poseidon::{Pow5Chip, Pow5Config, primitives::P128Pow5T3},
    sinsemilla::chip::{SinsemillaChip, SinsemillaConfig},
    utilities::lookup_range_check::{LookupRangeCheck, LookupRangeCheckConfig},
};
use orchard_legacy::halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance},
};
use orchard_legacy::pasta_curves::{
    arithmetic::CurveAffine,
    group::{
        Curve, GroupEncoding,
        ff::{Field, PrimeField},
    },
    pallas,
};
use proptest::prelude::*;

// Matches the exported chips' documented column layout and Sinsemilla table size.
const ADVICE_COLUMNS: usize = 10;
const FIXED_COLUMNS: usize = 8;
const CIRCUIT_K: u32 = 11;
const PK_X: usize = 0;
const PK_Y: usize = 1;
const CM_X: usize = 2;
const CM_Y: usize = 3;
const NF: usize = 4;

type Sinsemilla = SinsemillaConfig<OrchardHashDomains, OrchardCommitDomains, OrchardFixedBases>;
#[derive(Clone, Debug)]
struct Config {
    advice: [Column<Advice>; ADVICE_COLUMNS],
    instance: Column<Instance>,
    ecc: EccConfig<OrchardFixedBases>,
    sinsemilla: Sinsemilla,
    ivk: CommitIvkConfig,
    note: NoteCommitConfig,
    add: AddConfig,
    poseidon: Pow5Config<pallas::Base, 3, 2>,
}
#[derive(Clone, Default)]
struct Composition {
    input: Option<(FullViewingKey, Scope, Note)>,
}

fn base(bytes: [u8; 32]) -> pallas::Base {
    pallas::Base::from_repr(bytes).unwrap()
}
fn scalar(bytes: [u8; 32]) -> pallas::Scalar {
    pallas::Scalar::from_repr(bytes).unwrap()
}
fn affine(bytes: [u8; 32]) -> pallas::Affine {
    pallas::Point::from_bytes(&bytes).unwrap().to_affine()
}

impl Circuit<pallas::Base> for Composition {
    type Config = Config;
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Config {
        let advice = core::array::from_fn(|_| meta.advice_column());
        let fixed = core::array::from_fn::<_, FIXED_COLUMNS, _>(|_| meta.fixed_column());
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        for a in advice {
            meta.enable_equality(a);
        }
        meta.enable_constant(fixed[0]);
        let lookup = (
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        );
        let range = LookupRangeCheckConfig::configure(meta, advice[9], lookup.0);
        let ecc = EccChip::configure(meta, advice, fixed, range);
        let sinsemilla = SinsemillaChip::configure(
            meta,
            advice[..5].try_into().unwrap(),
            advice[6],
            fixed[0],
            lookup,
            range,
            false,
        );
        let second = SinsemillaChip::configure(
            meta,
            advice[5..].try_into().unwrap(),
            advice[7],
            fixed[1],
            lookup,
            range,
            false,
        );
        let ivk = CommitIvkChip::configure(meta, advice);
        let note = NoteCommitChip::configure(meta, advice, second);
        let add = AddChip::configure(meta, advice[7], advice[8], advice[6]);
        let poseidon = Pow5Chip::configure::<P128Pow5T3>(
            meta,
            advice[6..9].try_into().unwrap(),
            advice[5],
            fixed[2..5].try_into().unwrap(),
            fixed[5..8].try_into().unwrap(),
        );
        Config {
            advice,
            instance,
            ecc,
            sinsemilla,
            ivk,
            note,
            add,
            poseidon,
        }
    }
    fn synthesize(
        &self,
        c: Config,
        mut layouter: impl Layouter<pallas::Base>,
    ) -> Result<(), Error> {
        let input = self.input.as_ref().map_or(Value::unknown(), Value::known);
        let ecc = EccChip::construct(c.ecc, CircuitVersion::AnchoredBase);
        SinsemillaChip::<OrchardHashDomains, OrchardCommitDomains, OrchardFixedBases>::load(
            c.sinsemilla.clone(),
            &mut layouter,
        )?;
        let sinsemilla = SinsemillaChip::construct(c.sinsemilla);
        let mut load = |name: &'static str, v: Value<pallas::Base>| {
            assign_free_advice(layouter.namespace(|| name), c.advice[0], v)
        };
        let ak = load(
            "validating key x",
            input.map(|(fvk, _, _)| {
                *affine(SpendValidatingKey::from(fvk.clone()).to_bytes())
                    .coordinates()
                    .unwrap()
                    .x()
            }),
        )?;
        let nk = load(
            "nullifier key",
            input.map(|(fvk, _, _)| base(fvk.nk().to_bytes())),
        )?;
        let rho = load("rho", input.map(|(_, _, note)| base(note.rho().to_bytes())))?;
        let psi = load(
            "psi",
            input.map(|(_, _, note)| base(note.rseed().voting_psi(&note.rho()).to_bytes())),
        )?;
        let value = load(
            "value",
            input.map(|(_, _, note)| pallas::Base::from(note.value().inner())),
        )?;
        let gd = NonIdentityPoint::new(
            ecc.clone(),
            layouter.namespace(|| "diversified base"),
            input.map(|(_, _, note)| affine(note.recipient().g_d().to_bytes())),
        )?;
        let pkd = NonIdentityPoint::new(
            ecc.clone(),
            layouter.namespace(|| "transmission key"),
            input.map(|(_, _, note)| affine(note.recipient().pk_d().to_bytes())),
        )?;
        let rivk = ScalarFixed::new(
            ecc.clone(),
            layouter.namespace(|| "rivk"),
            input.map(|(fvk, scope, _)| scalar(fvk.rivk(*scope).to_bytes())),
        )?;
        let ivk = commit_ivk(
            sinsemilla.clone(),
            ecc.clone(),
            CommitIvkChip::construct(c.ivk),
            layouter.namespace(|| "incoming key commitment"),
            ak,
            nk.clone(),
            rivk,
        )?;
        let ivk = ScalarVar::from_base(
            ecc.clone(),
            layouter.namespace(|| "incoming key scalar"),
            ivk.inner(),
        )?;
        let (derived_pkd, _) = gd.mul(layouter.namespace(|| "address ownership"), ivk)?;
        derived_pkd.constrain_equal(
            layouter.namespace(|| "address must belong to viewing key"),
            &pkd,
        )?;
        layouter.constrain_instance(derived_pkd.inner().x().cell(), c.instance, PK_X)?;
        layouter.constrain_instance(derived_pkd.inner().y().cell(), c.instance, PK_Y)?;
        let rcm = ScalarFixed::new(
            ecc.clone(),
            layouter.namespace(|| "note trapdoor"),
            input.map(|(_, _, note)| {
                let rho = note.rho();
                let seed = note.rseed();
                let recipient = note.recipient();
                let pkd = NonIdentityPallasPoint::from_bytes(&recipient.pk_d().to_bytes()).unwrap();
                let trapdoor = match note.version() {
                    NoteVersion::V2 => seed.rcm_v2(&rho),
                    NoteVersion::V3 => seed.voting_rcm_v3(
                        &rho,
                        &recipient.g_d(),
                        &pkd,
                        note.value(),
                        &seed.voting_psi(&rho),
                    ),
                };
                scalar(trapdoor.to_bytes())
            }),
        )?;
        let cm = note_commit(
            layouter.namespace(|| "note commitment"),
            sinsemilla,
            ecc.clone(),
            NoteCommitChip::construct(c.note),
            gd.inner(),
            pkd.inner(),
            value,
            rho.clone(),
            psi.clone(),
            rcm,
        )?;
        layouter.constrain_instance(cm.inner().x().cell(), c.instance, CM_X)?;
        layouter.constrain_instance(cm.inner().y().cell(), c.instance, CM_Y)?;
        let nf = derive_nullifier(
            layouter.namespace(|| "nullifier"),
            Pow5Chip::construct(c.poseidon),
            AddChip::construct(c.add),
            ecc,
            rho,
            &psi,
            &cm,
            nk,
        )?;
        layouter.constrain_instance(nf.inner().cell(), c.instance, NF)
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1))]
    #[test]
    fn public_gadgets_match_native_values_and_reject_altered_claims(sk in arb_spending_key()) {
        let fvk = FullViewingKey::from(&sk);
        for scope in [Scope::External, Scope::Internal] {
            let address = fvk.address(Diversifier::from_bytes([0; 11]), scope);
            let rho = Rho::from_bytes(&pallas::Base::ONE.to_repr()).unwrap();
            // Fixed fixture seed; production callers require properly sourced note randomness.
            let seed = RandomSeed::from_bytes([7; 32], &rho).unwrap();
            for value in [0, 1, u64::MAX] {
                for version in [NoteVersion::V2, NoteVersion::V3] {
                    let note = Note::from_parts(address, NoteValue::from_raw(value), rho, seed, version).unwrap();
                    let pk = affine(note.recipient().pk_d().to_bytes());
                    let cm = affine(note.commitment().to_bytes());
                    let claims = vec![*pk.coordinates().unwrap().x(), *pk.coordinates().unwrap().y(), *cm.coordinates().unwrap().x(), *cm.coordinates().unwrap().y(), base(note.nullifier(&fvk).to_bytes())];
                    let circuit = Composition { input: Some((fvk.clone(), scope, note)) };
                    MockProver::run(CIRCUIT_K, &circuit, vec![claims.clone()]).unwrap().assert_satisfied();
                    for offset in [PK_X, CM_X, NF] {
                        let mut altered = claims.clone(); altered[offset] += pallas::Base::ONE;
                        prop_assert!(MockProver::run(CIRCUIT_K, &circuit, vec![altered]).unwrap().verify().is_err());
                    }
                }
            }
        }
    }
}
