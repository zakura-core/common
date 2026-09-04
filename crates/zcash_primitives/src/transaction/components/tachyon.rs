//! Functions for parsing and serialization of Tachyon transaction components.

use corez::io::{self, Read, Write};

use zcash_tachyon::TachyonBundle;

/// Reads a Tachyon bundle from a V7 transaction.
pub fn read_v7_bundle<R: Read>(reader: R) -> io::Result<TachyonBundle> {
    TachyonBundle::read(reader)
}

/// Writes a Tachyon bundle in a V7 transaction.
pub fn write_v7_bundle<W: Write>(bundle: &TachyonBundle, writer: W) -> io::Result<()> {
    bundle.write(writer)
}
