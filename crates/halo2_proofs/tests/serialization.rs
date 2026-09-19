use std::io::{self, Cursor, ErrorKind, Read};

use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value, floor_planner::V1},
    pasta::{EqAffine, Fp},
    plonk::{
        Advice, Circuit, CircuitConfigCache, Column, ConstraintSystem, Error, Expression, Instance,
        ProvingKey, Selector, SingleVerifier, TableColumn, VerifyingKey, create_proof, keygen_pk,
        keygen_vk, verify_proof,
    },
    poly::{Rotation, commitment::Params},
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use rand::{SeedableRng, rngs::StdRng};

const K: u32 = 5;
const N: usize = 1 << K;
const FIXED: usize = 4; // Table, complex selector, four-selector family, overlapping selector.
const PERMUTATIONS: usize = 3;
const SELECTORS: usize = 6;
const POINT_BYTES: usize = 32;
const SCALAR_BYTES: usize = 32;
const SELECTOR_START: usize = 5 + (FIXED + PERMUTATIONS) * POINT_BYTES;
const VK_LEN: usize = SELECTOR_START + SELECTORS * (N / 8);
const POLY_LEN: usize = 4 + N * SCALAR_BYTES;
const PK_LEN: usize = VK_LEN + (FIXED + PERMUTATIONS) * POLY_LEN;
const ROWS: [usize; 4] = [0, 7, 8, 17];

#[derive(Clone)]
struct Config {
    advice: [Column<Advice>; 2],
    instance: Column<Instance>,
    selectors: [Selector; SELECTORS],
    table: TableColumn,
}

#[derive(Clone, Copy)]
struct TestCircuit<const READ_ONLY: bool, const REQUIRE_CACHE: bool = false>;

impl<const READ_ONLY: bool, const REQUIRE_CACHE: bool> Circuit<Fp>
    for TestCircuit<READ_ONLY, REQUIRE_CACHE>
{
    type Config = Config;
    type FloorPlanner = V1;
    const CACHE_CONFIGURATION: bool = true;

    fn without_witnesses(&self) -> Self {
        assert!(!READ_ONLY, "reading a key must not request witnesses");
        *self
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Config {
        assert!(!REQUIRE_CACHE, "configuration cache not reused");
        let advice = std::array::from_fn(|_| meta.advice_column());
        let instance = meta.instance_column();
        for column in advice {
            meta.enable_equality(column);
        }
        meta.enable_equality(instance);
        let selectors = std::array::from_fn(|i| match i {
            5 => meta.complex_selector(),
            _ => meta.selector(),
        });
        let table = meta.lookup_table_column();
        for (i, selector) in selectors[..4].iter().enumerate() {
            meta.create_gate("selector family", |meta| {
                let a = meta.query_advice(advice[0], Rotation::cur());
                let expected = Expression::Constant(Fp::from(i as u64 + 1));
                vec![meta.query_selector(*selector) * (a - expected)]
            });
        }
        // Allow all four disjoint linear gates to share one compressed selector column.
        meta.set_minimum_degree(5);
        meta.create_gate("overlapping selector", |meta| {
            let a = meta.query_advice(advice[0], Rotation::cur());
            let b = meta.query_advice(advice[1], Rotation::cur());
            vec![meta.query_selector(selectors[4]) * (a - b)]
        });
        meta.lookup(|meta| {
            let a = meta.query_advice(advice[0], Rotation::cur());
            vec![(meta.query_selector(selectors[5]) * a, table)]
        });
        Config {
            advice,
            instance,
            selectors,
            table,
        }
    }

    fn cache_configuration(config: &Config) -> Option<CircuitConfigCache> {
        Some(CircuitConfigCache::new(config.clone()))
    }

    fn configuration_from_cache(cache: &CircuitConfigCache) -> Option<Config> {
        cache.clone_config()
    }

    fn synthesize(&self, config: Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        assert!(!READ_ONLY, "reading a key must not synthesize");
        layouter.assign_table(
            || "lookup table",
            |mut table| {
                for row in 0..=4 {
                    let value = Value::known(Fp::from(row as u64));
                    table.assign_cell(|| "value", config.table, row, || value)?;
                }
                Ok(())
            },
        )?;
        let public = layouter.assign_region(
            || "selectors and copies",
            |mut region| {
                let mut public = None;
                for (i, row) in ROWS.into_iter().enumerate() {
                    config.selectors[i].enable(&mut region, row)?;
                    config.selectors[4].enable(&mut region, row)?;
                    config.selectors[5].enable(&mut region, row)?;
                    let value = Value::known(Fp::from(i as u64 + 1));
                    let a = region.assign_advice(|| "a", config.advice[0], row, || value)?;
                    let b = region.assign_advice(|| "b", config.advice[1], row, || value)?;
                    region.constrain_equal(a.cell(), b.cell())?;
                    if i == 0 {
                        public = Some(a.cell());
                    }
                }
                Ok(public.unwrap())
            },
        )?;
        layouter.constrain_instance(public, config.instance, 0)
    }
}

fn keys<C: Circuit<Fp, Config: Send> + Sync>(
    circuit: &C,
) -> (Params<EqAffine>, ProvingKey<EqAffine>) {
    let params = Params::new(K);
    let vk = keygen_vk(&params, circuit).unwrap();
    let pk = keygen_pk(&params, vk, circuit).unwrap();
    (params, pk)
}

fn buffer(write: impl FnOnce(&mut Cursor<&mut [u8]>) -> io::Result<()>) -> Vec<u8> {
    let mut storage = [0; PK_LEN];
    let mut writer = Cursor::new(storage.as_mut_slice());
    write(&mut writer).unwrap();
    let len = writer.position() as usize;
    storage[..len].to_vec()
}

fn prove_and_verify(params: &Params<EqAffine>, pk: &ProvingKey<EqAffine>) -> Vec<u8> {
    let instances: &[&[&[Fp]]] = &[&[&[Fp::ONE]], &[&[Fp::ONE]]];
    let mut storage = [0; 16 * 1024];
    let mut transcript =
        Blake2bWrite::<_, _, Challenge255<_>>::init(Cursor::new(storage.as_mut_slice()));
    create_proof(
        params,
        pk,
        &[TestCircuit::<false, true>; 2],
        instances,
        StdRng::seed_from_u64(0x415),
        &mut transcript,
    )
    .unwrap();
    let len = transcript.finalize().position() as usize;
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&storage[..len]);
    verify_proof(
        params,
        pk.get_vk(),
        SingleVerifier::new(params),
        instances,
        &mut transcript,
    )
    .unwrap();
    storage[..len].to_vec()
}

#[test]
fn roundtrip_proofs_and_wire_layout() {
    let (params, pk) = keys(&TestCircuit::<false>);
    let vk_bytes = buffer(|writer| pk.get_vk().write(writer));
    let pk_bytes = buffer(|writer| pk.write(writer));
    assert_eq!(vk_bytes.len(), VK_LEN);
    assert_eq!(pk_bytes.len(), PK_LEN);
    assert_eq!(&pk_bytes[..VK_LEN], vk_bytes);
    assert_eq!(&vk_bytes[..5], &[K as u8, FIXED as u8, 0, 0, 0]);
    // Activations cross byte boundaries and are packed LSB first, in allocation order.
    assert_eq!(
        &vk_bytes[SELECTOR_START..],
        &[
            1, 0, 0, 0, 128, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 129, 1, 2, 0, 129, 1, 2, 0,
        ]
    );
    for polynomial in pk_bytes[VK_LEN..].chunks_exact(POLY_LEN) {
        assert_eq!(&polynomial[..4], &(N as u32).to_le_bytes());
    }
    // Concatenated keys must leave the next key and trailing bytes untouched.
    let bytes = [vk_bytes.as_slice(), pk_bytes.as_slice(), &[0xde, 0xad]].concat();
    let mut reader = Cursor::new(bytes.as_slice());
    let vk = VerifyingKey::<EqAffine>::read::<_, TestCircuit<true>>(&mut reader).unwrap();
    assert_eq!(reader.position() as usize, VK_LEN);
    let restored = ProvingKey::<EqAffine>::read::<_, TestCircuit<true>>(&mut reader).unwrap();
    assert_eq!(reader.position() as usize, VK_LEN + PK_LEN);
    let mut trailing = [0; 2];
    reader.read_exact(&mut trailing).unwrap();
    assert_eq!(trailing, [0xde, 0xad]);
    assert_eq!(buffer(|writer| vk.write(writer)), vk_bytes);
    assert_eq!(buffer(|writer| restored.write(writer)), pk_bytes);
    let fresh_params = Params::new(K);
    let regenerated = keygen_pk(&fresh_params, vk, &TestCircuit::<false>).unwrap();
    assert_eq!(buffer(|writer| regenerated.write(writer)), pk_bytes);
    let expected = prove_and_verify(&params, &pk);
    // Restored keys rebuild V1 floor plans and reuse cached configurations.
    for key in [&restored, &restored, &regenerated] {
        assert_eq!(prove_and_verify(&fresh_params, key), expected);
    }
}

#[test]
fn malformed_keys_and_writer_errors() {
    let (_, pk) = keys(&TestCircuit::<false>);
    for vk_only in [true, false] {
        let write = |writer: &mut Cursor<&mut [u8]>| {
            if vk_only {
                pk.get_vk().write(writer)
            } else {
                pk.write(writer)
            }
        };
        let bytes = buffer(write);
        let check = |bytes: &[u8], kind| {
            let mut reader = Cursor::new(bytes);
            let result = if vk_only {
                VerifyingKey::<EqAffine>::read::<_, TestCircuit<true>>(&mut reader).map(|_| ())
            } else {
                ProvingKey::<EqAffine>::read::<_, TestCircuit<true>>(&mut reader).map(|_| ())
            };
            assert_eq!(result.unwrap_err().kind(), kind);
        };
        // Unsupported base/extended domains and insufficient rows fail before allocation.
        for k in [(Fp::S + 1) as u8, Fp::S as u8, 0, 1] {
            check(&[k], ErrorKind::InvalidData);
        }
        for count in [0, (SELECTORS + 2) as u32, u32::MAX] {
            let mut bad = bytes[..5].to_vec();
            bad[1..5].copy_from_slice(&count.to_le_bytes());
            check(&bad, ErrorKind::InvalidData);
        }
        // A plausible count must still agree with actual selector compression.
        let mut bad = bytes.clone();
        bad[1..5].copy_from_slice(&((FIXED + 1) as u32).to_le_bytes());
        bad.splice(5..5, bytes[5..5 + POINT_BYTES].iter().copied());
        check(&bad, ErrorKind::InvalidData);
        let mut bad = bytes.clone();
        bad[SELECTOR_START + N / 8] |= 1; // Force two family selectors to collide.
        check(&bad, ErrorKind::InvalidData);
        for offset in [5, 5 + FIXED * POINT_BYTES] {
            let mut bad = bytes.clone();
            bad[offset..offset + POINT_BYTES].fill(0xff);
            check(&bad, ErrorKind::InvalidData);
        }
        for end in [0, 4, POINT_BYTES, SELECTOR_START - 1, VK_LEN - 1] {
            check(&bytes[..end], ErrorKind::UnexpectedEof);
        }
        if !vk_only {
            check(&bytes[..PK_LEN - 1], ErrorKind::UnexpectedEof);
            for offset in [VK_LEN, VK_LEN + FIXED * POLY_LEN] {
                for length in [0, N as u32 - 1, N as u32 + 1, u32::MAX] {
                    let mut bad = bytes.clone();
                    bad[offset..offset + 4].copy_from_slice(&length.to_le_bytes());
                    check(&bad, ErrorKind::InvalidData);
                }
                let mut bad = bytes.clone();
                bad[offset + 4..offset + 4 + SCALAR_BYTES].fill(0xff);
                check(&bad, ErrorKind::InvalidData);
                for end in [offset + 3, offset + 4, offset + POLY_LEN - 1] {
                    check(&bytes[..end], ErrorKind::UnexpectedEof);
                }
            }
        }
        for len in [0, SELECTOR_START - 1, bytes.len() - 1] {
            let mut storage = [0; PK_LEN];
            let error = write(&mut Cursor::new(&mut storage[..len])).unwrap_err();
            assert_eq!(error.kind(), ErrorKind::WriteZero);
            assert_eq!(&storage[..len], &bytes[..len]);
        }
    }
}

#[derive(Clone, Copy)]
struct MinimalCircuit<const EQUALITY: bool>;

impl<const EQUALITY: bool> Circuit<Fp> for MinimalCircuit<EQUALITY> {
    type Config = ();
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        assert!(!EQUALITY, "reading a key must not request witnesses");
        *self
    }
    fn configure(meta: &mut ConstraintSystem<Fp>) {
        if EQUALITY {
            let advice = meta.advice_column();
            meta.enable_equality(advice);
        }
    }
    fn synthesize(&self, _: (), _: impl Layouter<Fp>) -> Result<(), Error> {
        assert!(!EQUALITY, "reading a key must not synthesize");
        Ok(())
    }
}

#[test]
fn empty_keys_without_selectors_or_polynomials() {
    let (_, pk) = keys(&MinimalCircuit::<false>);
    let expected = [K as u8, 0, 0, 0, 0];
    assert_eq!(buffer(|writer| pk.get_vk().write(writer)), expected);
    assert_eq!(buffer(|writer| pk.write(writer)), expected);
    let mut reader = Cursor::new(expected.as_slice());
    let vk = VerifyingKey::<EqAffine>::read::<_, MinimalCircuit<false>>(&mut reader).unwrap();
    assert_eq!(reader.position(), 5);
    reader.set_position(0);
    let pk = ProvingKey::<EqAffine>::read::<_, MinimalCircuit<false>>(&mut reader).unwrap();
    assert_eq!(reader.position(), 5);
    assert_eq!(buffer(|writer| vk.write(writer)), expected);
    assert_eq!(buffer(|writer| pk.write(writer)), expected);
}

#[test]
#[cfg(target_pointer_width = "64")]
fn truncated_large_domain_pk_rejects_before_fft_allocation() {
    use group::{CurveAffine, GroupEncoding};

    // A valid degree-three extended domain, with no fixed polynomials. Premature
    // FFT allocation would consume tens of GiB before the missing permutation is read.
    let mut bytes = [0; 5 + POINT_BYTES + 4];
    bytes[0] = (Fp::S - 1) as u8;
    bytes[5..5 + POINT_BYTES].copy_from_slice(EqAffine::identity().to_bytes().as_ref());
    bytes[5 + POINT_BYTES..].copy_from_slice(&(1u32 << (Fp::S - 1)).to_le_bytes());
    for end in [5 + POINT_BYTES, bytes.len()] {
        let mut reader = Cursor::new(&bytes[..end]);
        let error =
            ProvingKey::<EqAffine>::read::<_, MinimalCircuit<true>>(&mut reader).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::UnexpectedEof);
        assert_eq!(reader.position() as usize, end);
    }
}
