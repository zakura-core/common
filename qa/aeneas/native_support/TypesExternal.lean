module
public import Aeneas
@[expose] public section
open Aeneas Std Result
abbrev core.array.iter.IntoIter (T : Type) (_N : Usize) := core.slice.iter.Iter T

structure core.slice.iter.ChunksExactMut (T : Type) where
  slice : Aeneas.Std.Slice T
  index : Nat
  chunkSize : Usize

structure core.slice.iter.Chunks (T : Type) where
  slice : Aeneas.Std.Slice T
  chunkSize : Usize
