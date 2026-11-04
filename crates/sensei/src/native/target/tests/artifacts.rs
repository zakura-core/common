//! Artifact compatibility pins and registry/embedding agreement.
//!
//! All digest literals are preserved expectations from the existing target tests.
//! Each pin names its input or construction and the byte representation hashed;
//! stored Montgomery records are distinct from canonical field/point encodings.

use crate::native::test_support::reduced_values;

use alloc::vec::Vec;

use sha2::{Digest, Sha256};

use crate::native::field::Fp;
use crate::native::generated_expressions::{
    GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, PREPARED_GATE_SELECTOR_FIXED_QUERY,
    PREPARED_GATE_SELECTOR_ROW, QueryKind, prepare_gate_selectors,
};
use crate::native::srs::PREPARED_POINTS;
#[cfg(feature = "verifier")]
use crate::static_data::bytes_of;

use super::super::{
    EXTENDED_N, FIXED_COLUMNS, FIXED_QUERIES, FIXED_TUPLES, FixedTarget, N, PreparedPolynomials,
    TargetError,
};
#[cfg(feature = "verifier")]
use super::super::{SIGMA_MAP, TUPLE_ASSIGNMENTS};

/// Pins the listed embedded payload bytes — generated into `OUT_DIR`
/// at build time — so any generator or raw-input change that
/// alters the static data is a deliberate, reviewed change. These digests
/// are pins *per stored form*, keyed by the descriptor-suffixed artifact
/// name; a second registered form earns its own pinned rows in a
/// compilation where it is the active form. The canonical-content pins
/// below are the representation-invariant complement. The separate selector
/// stream pin reduces values before hashing their Montgomery records.
#[test]
#[cfg(feature = "verifier")]
fn embedded_static_files_are_pinned() {
    let mut pinned: Vec<(&str, &[u8], &str)> = alloc::vec![
        (
            // Stored VerifierCommitments record: current commitments derived by
            // sensei-artifacts::points plus raw verifier-fixed/insecure.points.
            concat!("verifier-commitments.", udon::stored_form!(), ".pod"),
            bytes_of(crate::native::verifier::VK_DATA),
            "7a8228564bb3d7f11a05e155659fc33fe573d9a8a02570cdadaa5505c73cbf91",
        ),
        (
            // Stored SRS affine records: raw srs-coefficient-bases.points,
            // its inverse group transform/prefix sums, and pinned W/U points.
            concat!("srs-points.", udon::stored_form!(), ".pod"),
            bytes_of(PREPARED_POINTS),
            "9e061a192b23a4d3bd1bcae33006e218994bee155e8d7614ec75e5db3844a9f4",
        ),
        (
            // Stored Pallas affine records decoded by sensei-artifacts::points
            // from data/raw/sinsemilla-generators.points.
            concat!("primitive-points.", udon::stored_form!(), ".pod"),
            bytes_of(crate::primitives::tables::sinsemilla_generators()),
            "906de85c834cf1c0ab6830465485444d04f1e7d43f682d73c94b2fbd1b16d683",
        ),
        (
            // Stored Vesta affine records from points::window_bases::generate_x:
            // shared window-table x values multiplied by Lagrange row bases.
            concat!("fixed-window-x-bases.", udon::stored_form!(), ".pod"),
            bytes_of(super::super::FIXED_WINDOW_X_BASES),
            "61960318fd206349dbbdd6f7b052fd80635217263339b605d06500929c9f55d8",
        ),
        (
            // Stored Vesta affine records from points::window_bases::generate_y:
            // shared window-table y values multiplied by Lagrange row bases.
            concat!("fixed-window-y-bases.", udon::stored_form!(), ".pod"),
            bytes_of(super::super::FIXED_WINDOW_Y_BASES),
            "694c8e4e4b85580b61de075d630a1adf2cd095580b6ff45d6671fefa9c0584f2",
        ),
        (
            // Stored Vesta affine records from points::window_bases::generate_u:
            // shared window-table u values multiplied by Lagrange row bases.
            concat!("fixed-window-u-bases.", udon::stored_form!(), ".pod"),
            bytes_of(super::super::FIXED_WINDOW_U_BASES),
            "cd6e2e604494739aeb55fafe25fc8869eebd903ca50fa8221f2649e5cc0d2fe4",
        ),
    ];
    pinned.reserve_exact(sensei_artifacts::ARTIFACTS.len());
    #[cfg(embed_window_tables)]
    pinned.push((
        // Stored Pallas x/y/u field records from sensei-shared's pinned
        // fixed-base/window construction, encoded by fixed_base_tables.
        concat!("window-tables.", udon::stored_form!(), ".pod"),
        bytes_of(super::super::WINDOW_TABLES),
        "7ec541152329466fa0f25fc12cbb38d781a08c3f285eb8a5afb09ca30b36b093",
    ));
    #[cfg(embed_fixed_cosets)]
    pinned.push((
        // Stored reduced Montgomery values in residue-major order from
        // polynomials::cosets: shared fixed columns and sparse fixed rows.
        concat!("fixed-cosets.", udon::stored_form!(), ".pod"),
        bytes_of(super::super::FIXED_COSETS),
        "25793e971697c0b0a0ea5824b82cf5e628b53c348899fb184052040a77dcf354",
    ));
    #[cfg(embed_sigma_cosets)]
    pinned.push((
        // Stored reduced Montgomery values in residue-major order from
        // polynomials::cosets, using data/raw/sigma-map.cells.
        concat!("sigma-cosets.", udon::stored_form!(), ".pod"),
        bytes_of(super::super::SIGMA_COSETS),
        "e394ee9fbb646611d9d31bd351f71b610ccbb0fbbba278d30166ab20c423488a",
    ));
    // Frozen complete-selector stream from fixed cosets and the generated
    // selector recipe: row-major reduced Montgomery records via bytes_of,
    // not canonical to_bytes encodings or an unreduced embedded payload.
    // Stream every mode, including on-demand, without allocating a matrix.
    let target = crate::test_codec::target();
    let mut selector_digest = Sha256::new();
    for row in 0..EXTENDED_N {
        selector_digest.update(bytes_of(
            &selector_row(target, row).map(|value| value.reduce()),
        ));
    }
    assert_eq!(
        hex::encode(selector_digest.finalize()),
        "61a8647803bc894bb4b784f757b42fde2c41f343dba717def9f5bd2639c3d950"
    );
    #[cfg(embed_fixed_coefficients)]
    pinned.push((
        // Stored reduced Montgomery coefficients from polynomials::coefficients:
        // inverse transforms of shared fixed columns and sparse fixed rows.
        concat!("fixed-coefficients.", udon::stored_form!(), ".pod"),
        bytes_of(super::super::FIXED_COEFFICIENTS),
        "e05e66c1bf7b5a54a85fefa0464c5cfd1f406c91f1684d8e7bce4d2ec75264ae",
    ));
    #[cfg(embed_sigma_coefficients)]
    pinned.push((
        // Stored reduced Montgomery coefficients from polynomials::coefficients:
        // inverse transforms of columns reconstructed from sigma-map.cells.
        concat!("sigma-coefficients.", udon::stored_form!(), ".pod"),
        bytes_of(super::super::SIGMA_COEFFICIENTS),
        "5065b6b4ffc0474c7ed21c09d1f4f7de55a4e23f5270f5e986bc3abbf4afd9a1",
    ));
    #[cfg(embed_instance_bases)]
    pinned.push((
        // Stored reduced Montgomery rows from polynomials::basis: populated
        // instance Lagrange coefficients, transposed by coefficient degree.
        concat!("instance-bases.", udon::stored_form!(), ".pod"),
        bytes_of(super::super::INSTANCE_BASES),
        "cf3cd1f5ded2322837cda5aaf0c1fb82d16eae31da401ab94b2ee7992386c20a",
    ));
    #[cfg(embed_boundaries)]
    pinned.push((
        // Stored reduced Montgomery extended-coset values from
        // polynomials::basis: l_0, l_last, then the active-row mask.
        concat!("boundaries.", udon::stored_form!(), ".pod"),
        bytes_of(super::super::BOUNDARY_POLYNOMIALS),
        "209b76547b81bc2d8f2cae89346b0079bae8ce39938c1af4776244bedf6323df",
    ));
    #[cfg(embed_fft_tables)]
    pinned.push((
        // Stored reduced Montgomery twiddles/finish scales from
        // sensei-artifacts::fft::generate_tables and sensei-shared's FFT layout.
        concat!("fft-tables.", udon::stored_form!(), ".pod"),
        bytes_of(crate::native::polynomial::FFT_TABLES),
        "9a463f0ff140017bb46a552e3ad698f30816e9af323dc8ecf1199f5d39ec753a",
    ));
    #[cfg(embed_expansion_scales)]
    pinned.push((
        // Stored reduced Montgomery coefficient-expansion scales from
        // sensei-artifacts::fft::generate_scales and the shared FFT layout.
        concat!("expansion-scales.", udon::stored_form!(), ".pod"),
        bytes_of(crate::native::polynomial::EXPANSION_SCALES),
        "8b0d85331a8f89ba1ddbc720214e7bdda25a4191e110e256e99f5094c5416871",
    ));
    pinned.extend([
        (
            // Stored reduced Montgomery tuple dictionary from
            // sensei-artifacts::fixed_columns' window rows and constant cells.
            concat!("fixed-tuples.", udon::stored_form!(), ".pod"),
            bytes_of(FIXED_TUPLES),
            "d7c140251ad9aec9dcf292d10f9b7af09d0bf623644b570c30804af3b6ab1695",
        ),
        (
            // Stored integer RowAssignment records from the same sparse-row
            // dictionary; no field or Montgomery encoding is involved.
            "tuple-assignments.pod",
            bytes_of(TUPLE_ASSIGNMENTS),
            "51912c9e571b260ec74dacfc50aea7a5413239ba05667b777b7de2a5209dc951",
        ),
        (
            // Stored u16 target-cell indices decoded from data/raw/sigma-map.cells
            // by raw::permutation; no field or Montgomery encoding is involved.
            "sigma-map.pod",
            bytes_of(SIGMA_MAP),
            "9bbab7da320859fa7e93349416f5dea183ccdc250bbcdc66e5461ae17b9138a1",
        ),
    ]);
    for (name, bytes, expected_digest) in pinned {
        assert_eq!(
            hex::encode(Sha256::digest(bytes)),
            expected_digest,
            "stored-byte digest mismatch for {name}"
        );
    }
}

/// Pins canonical little-endian field encodings of the embedded SRS/Sinsemilla
/// coordinates and fixed tuples, with the labels and ordering below. The sources
/// are the raw coefficient/Sinsemilla points, derived Lagrange bases/prefix sums,
/// pinned auxiliary generators, and the sparse fixed-row construction.
/// Unlike the stored-byte digests above,
/// these are invariant across at-rest representations: a future stored
/// form must reproduce these exact canonical values even though every
/// stored byte changes. This is the existing content pin, not a digest of the
/// raw input files. (The coefficient matrices are pinned in canonical
/// form by the prepared-content digest test.)
#[test]
fn embedded_data_canonical_content_is_pinned() {
    fn absorb_base(digest: &mut Sha256, base: &udon::curve::VestaAffine) {
        let (x, y) = base.coordinates();
        digest.update(x.to_bytes());
        digest.update(y.to_bytes());
    }

    let mut digest = Sha256::new();
    digest.update(b"prepared points");
    for table in [
        &PREPARED_POINTS.coefficient_bases,
        &PREPARED_POINTS.lagrange_bases,
        &PREPARED_POINTS.lagrange_prefix_sums,
    ] {
        for base in table {
            absorb_base(&mut digest, base);
        }
    }
    for point in crate::primitives::tables::sinsemilla_generators() {
        let (x, y) = point.coordinates();
        digest.update(x.to_bytes());
        digest.update(y.to_bytes());
    }
    for point in [
        &PREPARED_POINTS.blind_generator,
        &PREPARED_POINTS.ipa_generator,
    ] {
        let (x, y) = point.coordinates();
        digest.update(x.to_bytes());
        digest.update(y.to_bytes());
    }
    digest.update(b"fixed tuples");
    for tuple in FIXED_TUPLES {
        for value in tuple {
            digest.update(value.to_bytes());
        }
    }
    assert_eq!(
        hex::encode(digest.finalize()),
        "eb4d630f91645d6ab396b1b25777d19014cf759e688dd911cdb217a177609749"
    );
}

/// The artifact registry and raw-input inventory in `sensei-artifacts`, the
/// embedding declarations here, and the `data/` directory describe the
/// same pipeline: the selected registry entries are exactly what this module
/// and the FFT module embed, matching the cfgs derived by `build.rs`.
/// Selected artifacts are generated at build time, none are checked in, and
/// `data/` holds exactly the raw layer. This checks registry↔embedding agreement;
/// host↔target form agreement needs no test, because a mismatch names a
/// file the generators did not emit and the embed paths fail the build.
#[test]
#[cfg(feature = "verifier")]
fn artifact_registry_matches_embedded_inventory() {
    let selected = crate::artifact_selection::selected();
    let mut embedded: Vec<String> = sensei_artifacts::ARTIFACTS
        .iter()
        .filter(|artifact| {
            selected.contains(&artifact.id)
                && artifact.form.is_none_or(|form| form == udon::STORED_FORM)
        })
        .map(|artifact| artifact.file_name())
        .collect();
    let mut expected: Vec<&str> = alloc::vec![
        concat!("primitive-points.", udon::stored_form!(), ".pod"),
        concat!("srs-points.", udon::stored_form!(), ".pod")
    ];
    expected.reserve_exact(sensei_artifacts::ARTIFACTS.len());
    expected.push(concat!(
        "verifier-commitments.",
        udon::stored_form!(),
        ".pod"
    ));
    #[cfg(embed_fixed_coefficients)]
    expected.push(concat!("fixed-coefficients.", udon::stored_form!(), ".pod"));
    #[cfg(embed_sigma_coefficients)]
    expected.push(concat!("sigma-coefficients.", udon::stored_form!(), ".pod"));
    #[cfg(embed_fixed_cosets)]
    expected.push(concat!("fixed-cosets.", udon::stored_form!(), ".pod"));
    #[cfg(embed_sigma_cosets)]
    expected.push(concat!("sigma-cosets.", udon::stored_form!(), ".pod"));
    #[cfg(embed_gate_selectors)]
    expected.push(concat!(
        "gate-selectors-complete.",
        udon::stored_form!(),
        ".pod"
    ));
    #[cfg(embed_window_tables)]
    expected.push(concat!("window-tables.", udon::stored_form!(), ".pod"));
    #[cfg(embed_instance_bases)]
    expected.push(concat!("instance-bases.", udon::stored_form!(), ".pod"));
    #[cfg(embed_boundaries)]
    expected.push(concat!("boundaries.", udon::stored_form!(), ".pod"));
    #[cfg(embed_commitment_tables)]
    expected.push(concat!("commitment-tables.", udon::stored_form!(), ".pod"));
    expected.extend([
        concat!("fixed-window-x-bases.", udon::stored_form!(), ".pod"),
        concat!("fixed-window-y-bases.", udon::stored_form!(), ".pod"),
        concat!("fixed-window-u-bases.", udon::stored_form!(), ".pod"),
        concat!("fixed-tuples.", udon::stored_form!(), ".pod"),
        "tuple-assignments.pod",
        "sigma-map.pod",
    ]);
    #[cfg(embed_fft_tables)]
    expected.push(concat!("fft-tables.", udon::stored_form!(), ".pod"));
    #[cfg(embed_expansion_scales)]
    expected.push(concat!("expansion-scales.", udon::stored_form!(), ".pod"));
    #[cfg(embed_gate_selectors)]
    embedded.push(concat!("gate-selectors-complete.", udon::stored_form!(), ".pod").to_owned());
    embedded.sort();
    expected.sort();
    assert_eq!(embedded, expected);
    let manifest = include_str!(concat!(env!("OUT_DIR"), "/artifact-manifest.json"));
    assert_eq!(
        manifest.contains(concat!(
            "gate-selectors-complete.",
            udon::stored_form!(),
            ".pod"
        )),
        cfg!(embed_gate_selectors)
    );
    for artifact in sensei_artifacts::ARTIFACTS {
        assert_eq!(
            manifest.contains(&format!("\"{}\"", artifact.file_name())),
            embedded.contains(&artifact.file_name())
        );
    }

    let data = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("data");
    for artifact in sensei_artifacts::ARTIFACTS {
        let name = artifact.file_name();
        assert!(
            !data.join(&name).exists(),
            "{name} is generated at build time and must not be checked in"
        );
    }

    let mut raw_names: Vec<&str> = sensei_artifacts::RAW_INPUTS.to_vec();
    raw_names.sort_unstable();
    let mut committed: Vec<String> = std::fs::read_dir(data.join("raw"))
        .expect("data/raw must exist")
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .filter(|name| !name.starts_with('.'))
        .collect();
    committed.sort();
    assert_eq!(
        committed, raw_names,
        "data/raw must hold exactly RAW_INPUTS"
    );

    let mut entries: Vec<String> = std::fs::read_dir(&data)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .filter(|name| !name.starts_with('.'))
        .collect();
    entries.sort();
    assert_eq!(entries, ["raw"], "data/ holds only the raw layer");
}

fn selector_queries(target: &FixedTarget, row: usize) -> [Fp; GATE_QUERY_COUNT] {
    core::array::from_fn(|frame_index| match GATE_QUERY_DESCRIPTORS[frame_index] {
        (QueryKind::Fixed, query_index) => {
            let query = FIXED_QUERIES[query_index];
            assert_eq!(query.rotation, 0);
            target.fixed_polynomials().cosets().column(query.column)[row]
        }
        (QueryKind::Advice | QueryKind::Instance, _) => <Fp>::ZERO,
    })
}

fn selector_row(target: &FixedTarget, row: usize) -> [Fp; PREPARED_GATE_SELECTOR_ROW] {
    target.gate_selectors().map_or_else(
        || prepare_gate_selectors(&selector_queries(target, row)),
        |rows| rows[row],
    )
}

/// Pins the existing prepared-polynomial content: fixed/sigma coefficients
/// and dense-row cosets derived from the fixed layout and sigma map. The stream
/// contains the labels and usize dimensions below, then canonical little-endian
/// field encodings via to_bytes, independent of stored Montgomery residues.
#[test]
fn prepared_polynomial_forms_are_pinned_and_dimension_checked() {
    let target = crate::test_codec::target();
    let fixed = target.fixed_polynomials();
    let sigma = target.sigma_polynomials();
    assert_eq!(fixed.coefficients().len(), FIXED_COLUMNS);
    assert_eq!(fixed.cosets().len(), FIXED_COLUMNS);
    assert_eq!(sigma.coefficients().len(), target.sigma_values().len());
    assert_eq!(sigma.cosets().len(), target.sigma_values().len());
    assert!(fixed.coefficients().iter().all(|column| column.len() == N));
    assert!(sigma.coefficients().iter().all(|column| column.len() == N));
    assert_eq!(fixed.cosets().collect_views().len(), FIXED_COLUMNS);
    assert_eq!(
        sigma.cosets().collect_views().len(),
        target.sigma_values().len()
    );
    let selector_query = FIXED_QUERIES[PREPARED_GATE_SELECTOR_FIXED_QUERY];
    assert_eq!(selector_query.rotation, 0);
    if let Some(rows) = target.gate_selectors() {
        assert_eq!(rows.len(), EXTENDED_N);
    }
    for row in 0..EXTENDED_N {
        assert_eq!(
            reduced_values(&selector_row(target, row)),
            reduced_values(&prepare_gate_selectors(&selector_queries(target, row)))
        );
    }
    fn column_views(columns: &[Vec<Fp>]) -> Vec<&[Fp]> {
        columns.iter().map(|column| &column[..]).collect()
    }
    // The residue-major store read back in dense row order, the layout the
    // digest and the dense oracle use.
    let dense_rows = |cosets: &super::super::CosetColumns| -> Vec<Vec<Fp>> {
        (0..cosets.len())
            .map(|index| {
                let column = cosets.column(index);
                (0..EXTENDED_N).map(|row| column[row]).collect()
            })
            .collect()
    };
    let fixed_dense = dense_rows(fixed.cosets());
    let sigma_dense = dense_rows(sigma.cosets());
    let mut digest = Sha256::new();
    for (label, columns) in [
        (
            b"fixed coefficients".as_slice(),
            fixed
                .coefficients()
                .iter()
                .map(|column| &column[..])
                .collect(),
        ),
        (b"fixed cosets".as_slice(), column_views(&fixed_dense)),
        (
            b"sigma coefficients".as_slice(),
            sigma
                .coefficients()
                .iter()
                .map(|column| &column[..])
                .collect(),
        ),
        (b"sigma cosets".as_slice(), column_views(&sigma_dense)),
    ] {
        let columns: Vec<&[Fp]> = columns;
        digest.update(label);
        digest.update(columns.len().to_le_bytes());
        for column in columns {
            digest.update(column.len().to_le_bytes());
            for value in column {
                digest.update(value.to_bytes());
            }
        }
    }
    let digest = hex::encode(digest.finalize());
    assert_eq!(
        digest,
        "026bbd7b7a27c73cded8213e55efa758172ecae043d7fe0a1ba3870f18af1859"
    );

    let (derived_fixed_coefficients, derived_fixed_cosets) =
        PreparedPolynomials::derive(target.fixed_values(), FIXED_COLUMNS).unwrap();
    let (derived_sigma_coefficients, derived_sigma_cosets) =
        PreparedPolynomials::derive(target.sigma_values(), target.sigma_values().len()).unwrap();
    assert_eq!(fixed.coefficients().len(), derived_fixed_coefficients.len());
    for (embedded, derived) in fixed.coefficients().iter().zip(&derived_fixed_coefficients) {
        assert_eq!(
            reduced_values(&(&embedded[..])),
            reduced_values(&(&derived[..]))
        );
    }
    assert_eq!(
        reduced_values(&(fixed_dense)),
        reduced_values(&(derived_fixed_cosets))
    );
    assert_eq!(sigma.coefficients().len(), derived_sigma_coefficients.len());
    for (embedded, derived) in sigma.coefficients().iter().zip(&derived_sigma_coefficients) {
        assert_eq!(
            reduced_values(&(&embedded[..])),
            reduced_values(&(&derived[..]))
        );
    }
    assert_eq!(
        reduced_values(&(sigma_dense)),
        reduced_values(&(derived_sigma_cosets))
    );

    assert!(matches!(
        PreparedPolynomials::derive(&target.fixed_values()[..1], FIXED_COLUMNS),
        Err(TargetError::Dimension)
    ));
}
