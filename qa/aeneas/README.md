# Aeneas proofs of Common's Udon arithmetic

This restoration layer covers native Fp/Fq arithmetic. The cumulative catalog checks
256 declarations against production revision
`30eeb939123414887642f1cdb60ea59ab13bdf7c`. Production Rust is unchanged.

The complete restoration is validated by fresh extraction, Lean compilation
and an exact axiom census; its evidence is added with the final field-path
commit. See RECOVERY.md for provenance and scope.

Use the compiler recipe in build_native_charon.py and run reproduce.py
with the tool pins in provenance.json.
