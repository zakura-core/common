//! Functions for parsing and serialization of Tachyon transaction components.

use corez::io::{self, Read, Write};

use zcash_tachyon::TachyonBundle;

/// Reads a Tachyon bundle from a V7 transaction.
pub fn read_v7_bundle<R: Read>(reader: R) -> io::Result<Option<TachyonBundle>> {
    Ok(match TachyonBundle::read(reader)? {
        TachyonBundle::NoBundle => None,
        bundle => Some(bundle),
    })
}

/// Writes a Tachyon bundle in a V7 transaction.
pub fn write_v7_bundle<W: Write>(bundle: Option<&TachyonBundle>, mut writer: W) -> io::Result<()> {
    match bundle {
        None => TachyonBundle::NoBundle.write(&mut writer),
        Some(bundle) => bundle.write(&mut writer),
    }
}
