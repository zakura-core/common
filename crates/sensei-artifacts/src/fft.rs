//! Optional FFT artifacts in the shared flat-array layout.

use sensei_shared::{K, N, fft as layout};
use udon::{
    fft::{Domain, ExpansionScaleNormalization, ExpansionScales, TablesMut},
    field::Fp,
};

use crate::{Error, context::Context, normalize_stored_montgomery};

pub(crate) fn generate_tables(_: &Context<'_>) -> Result<Vec<u8>, Error> {
    let mut values = vec![<Fp>::ZERO; layout::TABLE_LEN];
    for plan_index in 0..layout::PLAN_COUNT {
        let domain = Domain::for_size(layout::plan_size(plan_index)).unwrap();
        let domain = if plan_index == 0 {
            domain.subgroup()
        } else {
            domain.coset()
        };
        let len = domain.size() / 2;
        let offset = layout::table_offset(plan_index);
        let tables = &mut values[offset..offset + 3 * len];
        let (forward, rest) = tables.split_at_mut(len);
        let (inverse, finish) = rest.split_at_mut(len);
        TablesMut {
            forward: Some(forward),
            inverse: Some(inverse),
            inverse_finish: Some(finish),
        }
        .prepare(domain);
    }
    normalize_stored_montgomery(&mut values);
    Ok(bento::bytes_of_slice(&values).to_vec())
}

pub(crate) fn generate_scales(_: &Context<'_>) -> Result<Vec<u8>, Error> {
    let mut values = vec![<Fp>::ZERO; layout::SCALE_LEN];
    for coset_index in 0..layout::PLAN_COUNT - 1 {
        let domain = Domain::new(K + coset_index as u32).unwrap().coset();
        let offset = layout::scale_offset(coset_index);
        ExpansionScales::prepare(
            N,
            domain,
            ExpansionScaleNormalization::Coefficients,
            &mut values[offset..offset + domain.size()],
        )
        .unwrap();
    }
    normalize_stored_montgomery(&mut values);
    Ok(bento::bytes_of_slice(&values).to_vec())
}
