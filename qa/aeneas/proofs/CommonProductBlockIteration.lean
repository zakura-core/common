import CommonProductBlockLoops

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem slice_pair_next_some {α β : Type}
    (lhs : Aeneas.Std.Slice α) (rhs : Aeneas.Std.Slice β) (i : Nat)
    (ha : i < lhs.length) (hb : i < rhs.length) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter α) (core.iter.traits.iterator.IteratorSliceIter β)
      ⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ = ok (some (lhs[i]'ha,rhs[i]'hb),⟨⟨lhs,i+1⟩,⟨rhs,i+1⟩⟩) := by
  simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.iter.traits.iterator.IteratorSliceIter,core.slice.iter.IteratorSliceIter.next,ha,hb]
  constructor <;> rfl

theorem slice_pair_next_none {α β : Type}
    (lhs : Aeneas.Std.Slice α) (rhs : Aeneas.Std.Slice β) (i : Nat) (ha : lhs.length ≤ i) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter α) (core.iter.traits.iterator.IteratorSliceIter β)
      ⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ = ok (none,⟨⟨lhs,i⟩,⟨rhs,i⟩⟩) := by
  simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.iter.traits.iterator.IteratorSliceIter,core.slice.iter.IteratorSliceIter.next,
    show ¬ i < lhs.length from by omega]

def addQuad {M S T : Type} (li ri : Usize) (columns : BatchColumns)
    (lhs : Quad M S) (rhs : Quad M T) : Result BatchColumns := do
  let a ← addAt 0#usize li ri columns lhs[0]! rhs[0]!
  let b ← addAt 1#usize li ri a lhs[1]! rhs[1]!
  let c ← addAt 2#usize li ri b lhs[2]! rhs[2]!
  addAt 3#usize li ri c lhs[3]! rhs[3]!

attribute [local irreducible] Std.bind
  CommonProductsAarch64.field.pasta.products.add_product

theorem quad_body_some_eq {M S T : Type} (li ri : Usize)
    (iter next : QuadIter M S T) (columns : BatchColumns) (lhs : Quad M S) (rhs : Quad M T)
    (hnext : core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (Quad M S))
      (core.iter.traits.iterator.IteratorSliceIter (Quad M T)) iter = ok (some (lhs,rhs),next)) :
    quadBody li ri iter columns = (do
      let out ← addQuad li ri columns lhs rhs
      ok (.cont (next,out))) := by
  unfold quadBody
  rw [hnext]
  simp only [Bind.bind,bind_ok,Std.uncurry_apply_pair]
  rw [UdonVerify.ProductPortable.array_four_eta_generic lhs,
    UdonVerify.ProductPortable.array_four_eta_generic rhs]
  unfold addQuad addAt
  simp [Array.index_mut_usize,Array.index_usize,Array.getElem!_Nat_eq,
    Bind.bind,Std.bind_assoc]

theorem tail_body_some_eq {M S T : Type} (li ri : Usize)
    (iter next : PairIter M S T) (columns : BatchColumns) (lhs : Element M S) (rhs : Element M T)
    (hnext : core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (Element M S))
      (core.iter.traits.iterator.IteratorSliceIter (Element M T)) iter = ok (some (lhs,rhs),next)) :
    tailBody li ri iter columns = (do
      let out ← addAt 0#usize li ri columns lhs rhs
      ok (.cont (next,out))) := by
  unfold tailBody addAt
  rw [hnext]
  simp only [Bind.bind,bind_ok,Std.uncurry_apply_pair,Std.bind_assoc]
  congr 1
  funext pair
  rcases pair with ⟨column,back⟩
  simp only [Std.uncurry,Std.bind_assoc,bind_ok]

#print axioms slice_pair_next_some
#print axioms slice_pair_next_none
#print axioms quad_body_some_eq
#print axioms tail_body_some_eq
end UdonVerify.ProductBlock
