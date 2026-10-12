module
public import NativeField.TypesExternal
@[expose] public section

namespace CommonProductsAarch64

/-- Remaining shared slices of a standard nonoverlapping chunk iterator. -/
structure core.slice.iter.Chunks (T : Type) where
  chunks : List (Aeneas.Std.Slice T)

end CommonProductsAarch64
