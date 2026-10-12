import CommonProductBlockPrimitives
import CommonProductAarch64ShortSteps

open Aeneas Std Result ControlFlow
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev Quad (M S : Type) := Array (Element M S) 4#usize
abbrev QuadIter (M S T : Type) := core.iter.adapters.zip.Zip
  (core.slice.iter.Iter (Quad M S)) (core.slice.iter.Iter (Quad M T))

def quadBody (li ri : Usize)
  {M : Type} {T1 : Type} {T2 : Type}
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter (Array
  (CommonProductsAarch64.field.pasta.PastaField M T1) 4#usize)) (core.slice.iter.Iter (Array
  (CommonProductsAarch64.field.pasta.PastaField M T2) 4#usize)))
  (self : Array (Array Std.U64 3#usize) 4#usize) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Iter (Array
    (CommonProductsAarch64.field.pasta.PastaField M T1) 4#usize)) (core.slice.iter.Iter (Array
    (CommonProductsAarch64.field.pasta.PastaField M T2) 4#usize))) × (Array (Array Std.U64 3#usize)
    4#usize)) (Array (Array Std.U64 3#usize) 4#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (Array
      (CommonProductsAarch64.field.pasta.PastaField M T1) 4#usize))
      (core.iter.traits.iterator.IteratorSliceIter (Array
      (CommonProductsAarch64.field.pasta.PastaField M T2) 4#usize)) iter
  match o with
  | none => ok (done self)
  | some p =>
    let (lhs, rhs) := p
    let (a, index_mut_back) ← Array.index_mut_usize self 0#usize
    let pf ← Array.index_usize lhs 0#usize
    let i ← Array.index_usize pf.limbs li
    let pf1 ← Array.index_usize rhs 0#usize
    let i1 ← Array.index_usize pf1.limbs ri
    let a1 ← CommonProductsAarch64.field.pasta.products.add_product a i i1
    let self1 := index_mut_back a1
    let (a2, index_mut_back1) ← Array.index_mut_usize self1 1#usize
    let pf2 ← Array.index_usize lhs 1#usize
    let i2 ← Array.index_usize pf2.limbs li
    let pf3 ← Array.index_usize rhs 1#usize
    let i3 ← Array.index_usize pf3.limbs ri
    let a3 ← CommonProductsAarch64.field.pasta.products.add_product a2 i2 i3
    let self2 := index_mut_back1 a3
    let (a4, index_mut_back2) ← Array.index_mut_usize self2 2#usize
    let pf4 ← Array.index_usize lhs 2#usize
    let i4 ← Array.index_usize pf4.limbs li
    let pf5 ← Array.index_usize rhs 2#usize
    let i5 ← Array.index_usize pf5.limbs ri
    let a5 ← CommonProductsAarch64.field.pasta.products.add_product a4 i4 i5
    let self3 := index_mut_back2 a5
    let (a6, index_mut_back3) ← Array.index_mut_usize self3 3#usize
    let pf6 ← Array.index_usize lhs 3#usize
    let i6 ← Array.index_usize pf6.limbs li
    let pf7 ← Array.index_usize rhs 3#usize
    let i7 ← Array.index_usize pf7.limbs ri
    let a7 ← CommonProductsAarch64.field.pasta.products.add_product a6 i6 i7
    let a8 := index_mut_back3 a7
    ok (cont (iter1, a8))

def tailBody (li ri : Usize)
  {M : Type} {T1 : Type} {T2 : Type}
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter
  (CommonProductsAarch64.field.pasta.PastaField M T1)) (core.slice.iter.Iter (CommonProductsAarch64.field.pasta.PastaField
  M T2))) (self : Array (Array Std.U64 3#usize) 4#usize) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Iter
    (CommonProductsAarch64.field.pasta.PastaField M T1)) (core.slice.iter.Iter
    (CommonProductsAarch64.field.pasta.PastaField M T2))) × (Array (Array Std.U64 3#usize) 4#usize))
    (Array (Array Std.U64 3#usize) 4#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (CommonProductsAarch64.field.pasta.PastaField M
      T1)) (core.iter.traits.iterator.IteratorSliceIter (CommonProductsAarch64.field.pasta.PastaField
      M T2)) iter
  match o with
  | none => ok (done self)
  | some p =>
    let (lhs, rhs) := p
    let (a, index_mut_back) ← Array.index_mut_usize self 0#usize
    let i ← Array.index_usize lhs.limbs li
    let i1 ← Array.index_usize rhs.limbs ri
    let a1 ← CommonProductsAarch64.field.pasta.products.add_product a i i1
    let a2 := index_mut_back a1
    ok (cont (iter1, a2))

def quadLoop {M S T : Type} (li ri : Usize) (iter : QuadIter M S T)
    (columns : BatchColumns) : Result BatchColumns :=
  loop (fun (it,cols) => quadBody li ri it cols) (iter,columns)

def tailLoop {M S T : Type} (li ri : Usize) (iter : PairIter M S T)
    (columns : BatchColumns) : Result BatchColumns :=
  loop (fun (it,cols) => tailBody li ri it cols) (iter,columns)

def accumulateColumn (li ri : Usize)
  {M : Type} {T1 : Type} {T2 : Type}
  (self : Array (Array Std.U64 3#usize) 4#usize)
  (lhs : Aeneas.Std.Slice (CommonProductsAarch64.field.pasta.PastaField M T1))
  (rhs : Aeneas.Std.Slice (CommonProductsAarch64.field.pasta.PastaField M T2)) :
  Result (Array (Array Std.U64 3#usize) 4#usize)
  := do
  let (lhs_quads, lhs_remainder) ← CommonProductsAarch64.core.slice.Slice.as_chunks 4#usize lhs
  let (rhs_quads, rhs_remainder) ← CommonProductsAarch64.core.slice.Slice.as_chunks 4#usize rhs
  let i ← core.slice.Slice.iter lhs_quads
  let iter ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.iter.traits.iterator.IteratorSliceIter (Array
      (CommonProductsAarch64.field.pasta.PastaField M T1) 4#usize))
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter (Array
      (CommonProductsAarch64.field.pasta.PastaField M T2) 4#usize)) i rhs_quads
  let self1 ← quadLoop li ri iter self
  let i1 ← core.slice.Slice.iter lhs_remainder
  let iter1 ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.iter.traits.iterator.IteratorSliceIter (CommonProductsAarch64.field.pasta.PastaField M
      T1)) (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
      (CommonProductsAarch64.field.pasta.PastaField M T2)) i1 rhs_remainder
  tailLoop li ri iter1 self1

end UdonVerify.ProductBlock
