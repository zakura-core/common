import CommonProductPortablePrimitives
import CommonProductChunkMath

open Aeneas Std Result
namespace UdonVerify.ProductPortable
open UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

instance elementInhabited {M S : Type} : Inhabited (Element M S) :=
  ⟨⟨Array.repeat 4#usize 0#u64, ()⟩⟩
instance sumInhabited {M : Type} : Inhabited (Sum M) :=
  ⟨⟨Array.repeat 8#usize 0#u64, 0#u64, ()⟩⟩

abbrev Lanes (M : Type) := Array (Sum M) 4#usize
abbrev ChunkIter (M S T : Type) := core.iter.adapters.zip.Zip
  (core.slice.iter.ChunksExact (Element M S)) (core.slice.iter.ChunksExact (Element M T))

def lanesInteger {M : Type} (lanes : Lanes M) : Nat :=
  sumInteger lanes[0]! + sumInteger lanes[1]! + sumInteger lanes[2]! + sumInteger lanes[3]!

theorem array_four_eta_generic {α : Type} [Inhabited α] (a : Array α 4#usize) :
    a = Array.make 4#usize [a[0]!, a[1]!, a[2]!, a[3]!] := by
  apply Aeneas.Std.Array.ext
  obtain ⟨a0,a1,a2,a3,ha⟩ := List.length_eq_four.mp (show a.val.length = 4 by simpa using a.property)
  simp [Array.getElem!_Nat_eq, Array.make_val, ha]

def fourSlice {α : Type} (a b c d : α) : Aeneas.Std.Slice α :=
  Aeneas.Std.Slice.from [a,b,c,d] (by scalar_tac)

def addFour {M S T : Type} (inst : Modulus M) (lanes : Lanes M)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) : Result (Lanes M) := do
  let a ← CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner true inst lanes[0]! lhs[0]! rhs[0]!
  let b ← CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner true inst lanes[1]! lhs[1]! rhs[1]!
  let c ← CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner true inst lanes[2]! lhs[2]! rhs[2]!
  let d ← CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner true inst lanes[3]! lhs[3]! rhs[3]!
  ok (Array.make 4#usize [a,b,c,d])

theorem chunk_next_some_eq {M S T : Type}
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (xs : List (Aeneas.Std.Slice (Element M S))) (ys : List (Aeneas.Std.Slice (Element M T)))
    (a : Aeneas.Std.Slice (Element M S)) (b : Aeneas.Std.Slice (Element M T)) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorChunksExact (Element M S))
      (core.iter.traits.iterator.IteratorChunksExact (Element M T))
      (⟨⟨lhs::xs,a⟩,⟨rhs::ys,b⟩⟩ : ChunkIter M S T) =
        ok (some (lhs,rhs),⟨⟨xs,a⟩,⟨ys,b⟩⟩) := by
  simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.iter.traits.iterator.IteratorChunksExact, core.slice.iter.IteratorChunksExact.next]

attribute [local irreducible] Std.bind
  CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner

/-- The four mutable Zip payloads equal four independent accumulator updates;
    the fifth iterator check exhausts the four lanes and cannot reach the guard. -/
theorem lanes_body_cons_eq {M S T : Type} (inst : Modulus M) (lanes : Lanes M)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (xs : List (Aeneas.Std.Slice (Element M S))) (ys : List (Aeneas.Std.Slice (Element M T)))
    (a : Aeneas.Std.Slice (Element M S)) (b : Aeneas.Std.Slice (Element M T))
    (ha : lhs.length = 4) (hb : rhs.length = 4) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2.body
      inst (⟨⟨lhs::xs,a⟩,⟨rhs::ys,b⟩⟩ : ChunkIter M S T) lanes = (do
        let out ← addFour inst lanes lhs rhs
        ok (.cont (⟨⟨xs,a⟩,⟨ys,b⟩⟩,out))) := by
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2.body
  rw [chunk_next_some_eq]
  simp only [Bind.bind, bind_ok, Std.uncurry_apply_pair]
  obtain ⟨a0,a1,a2,a3,hlhs⟩ := List.length_eq_four.mp ha
  obtain ⟨b0,b1,b2,b3,hrhs⟩ := List.length_eq_four.mp hb
  have hlhsSlice : lhs = fourSlice a0 a1 a2 a3 :=
    Aeneas.Std.Slice.ext _ _ (by simpa only [fourSlice, Aeneas.Std.Slice.from_val] using hlhs)
  have hrhsSlice : rhs = fourSlice b0 b1 b2 b3 :=
    Aeneas.Std.Slice.ext _ _ (by simpa only [fourSlice, Aeneas.Std.Slice.from_val] using hrhs)
  subst lhs rhs
  rw [array_four_eta_generic lanes]
  unfold addFour
  simp (config := { maxSteps := 1000000 }) [fourSlice, lift, Array.to_slice_mut, Array.to_slice,
    core.slice.Slice.iter_mut, core.slice.Slice.iter, mutableZipCtor,
    core.iter.traits.iterator.Iterator.zip.trait_default, core.iter.traits.iterator.Iterator.zip.default,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    core.iter.traits.collect.IntoIterator.Blanket,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter,
    CommonProductsPortable.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair,
    mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.iter.traits.iterator.IteratorSliceIter,
    Bind.bind, bind_tc_eq, Std.uncurry, Std.bind_assoc, Array.from_slice, Slice.setAtNat]
  with_unfolding_all rfl

#print axioms array_four_eta_generic
#print axioms chunk_next_some_eq
#print axioms lanes_body_cons_eq
end UdonVerify.ProductPortable
