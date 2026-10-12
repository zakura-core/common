module
public import NativeField.TypesExternal
@[expose] public section

open Aeneas Std Result
namespace CommonProductDotIter

/-- The existing supertrait dictionary and its actual dispatched operations.
    Keep length and zip abstract: Rust iterators may override either operation. -/
structure ExactIteratorOps (Self Item : Type) where
  iteratorInst : core.iter.traits.iterator.Iterator Self Item
  len : Self → Result Usize
  zip : {U OtherItem IntoIter : Type} →
    core.iter.traits.collect.IntoIterator U OtherItem IntoIter →
    Self → U → Result (core.iter.adapters.zip.Zip Self IntoIter)

end CommonProductDotIter
