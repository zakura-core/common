module
public import KernelSlice.Types
public import Word.FunsExternal
@[expose] public section

open Aeneas Std

/-- The Rust Ordering discriminants, checked against the Charon export. -/
instance : Discriminant Ordering I8 where
  read_discriminant
    | .lt => (-1)#i8
    | .eq => 0#i8
    | .gt => 1#i8
