//! Reusable primitive tables, without proof runtime or SRS initialization.
// The artifact generator validates the points. Embedding checks the POD layout
// and preserves those trusted values without decoding points at runtime.
crate::static_data::embed_struct! {
    static POINTS: sensei_shared::PrimitivePointsFile = artifact_path!(primitive_points);
}

pub(crate) fn sinsemilla_generators()
-> &'static [udon::curve::PallasAffine; sensei_shared::generators::SINSEMILLA_TABLE_ROWS] {
    &POINTS.sinsemilla_generators
}
