//! Affine-only expanded commitment tables selected by the consumer's policy.
use crate::{Error, context::Context};
use sensei_shared::commitment_tables::{self as tables, Codebook, SECTIONS};
use udon::curve::VestaAffine;

pub(crate) fn generate(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    let config = context.commitment_tables;
    config.validate();
    if config.embedded_entries() == 0 {
        return Ok(Vec::new());
    }
    let points = crate::points::prepared_srs_points(context)?;
    let books: [Option<Codebook>; 3] = core::array::from_fn(|i| {
        config
            .srs
            .iter()
            .enumerate()
            .any(|(section, p)| config.embeds(section) && p.table.alpha_width() == i as u8 + 5)
            .then(|| Codebook::new(i as u8 + 5))
    });
    let fixed = [
        points.blind_generator,
        points.ipa_generator,
        points.coefficient_bases[0],
        tables::repeated_coordinate_base(&points.lagrange_bases),
    ];
    let mut result = Vec::with_capacity(config.embedded_entries() * 64);
    for section in 0..SECTIONS {
        if !config.embeds(section) || config.entries(section) == 0 {
            continue;
        }
        let entries: Vec<VestaAffine> = if section < 2 {
            let policy = config.srs[section];
            let book = policy
                .table
                .alpha_width()
                .checked_sub(5)
                .and_then(|i| books[i as usize].as_ref());
            let bases = if section == 0 {
                &points.coefficient_bases
            } else {
                &points.lagrange_bases
            };
            tables::srs(bases, policy.table, book)
        } else if section < 6 {
            tables::fixed(&fixed[section - 2], config.fixed[section - 2])
        } else if section == 17 {
            tables::odd(&points.coefficient_bases, config.folding.unwrap().width)
        } else {
            tables::fixed(
                &points.coefficient_bases[1 << (section - 6)],
                config.sparse.unwrap(),
            )
        };
        assert_eq!(entries.len(), config.entries(section));
        result.extend_from_slice(bento::bytes_of_slice(&entries));
    }
    assert_eq!(result.len(), config.embedded_entries() * 64);
    Ok(result)
}
