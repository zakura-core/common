import NativeProductMergeBound
open Aeneas Std Result
namespace UdonVerify.Native
set_option maxHeartbeats 200000
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
open NativeField.zakura_udon.field.pasta.word

def mergeExpansion {M : Type} (inst : Modulus M) (sum other : Sum M) : Result (Sum M) := do
  let (r0,c0) ← adc sum.wide[0]! other.wide[0]! 0#u64
  let (r1,c1) ← adc sum.wide[1]! other.wide[1]! c0
  let (r2,c2) ← adc sum.wide[2]! other.wide[2]! c1
  let (r3,c3) ← adc sum.wide[3]! other.wide[3]! c2
  let (r4,c4) ← adc sum.wide[4]! other.wide[4]! c3
  let (r5,c5) ← adc sum.wide[5]! other.wide[5]! c4
  let (r6,c6) ← adc sum.wide[6]! other.wide[6]! c5
  let (r7,c7) ← adc sum.wide[7]! other.wide[7]! c6
  let (carry,overflow) ← adc sum.carry other.carry c7
  NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow inst
    {sum with wide:=Array.make 8#usize [r0,r1,r2,r3,r4,r5,r6,r7],carry} overflow

theorem merge_expansion_eq {M : Type} (inst : Modulus M) (sum other : Sum M) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.merge inst sum other =
      mergeExpansion inst sum other := by
  rcases sum with ⟨a,carry,marker⟩
  rcases other with ⟨b,otherCarry,otherMarker⟩
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,ha⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : U64,
      a=Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7] :=
    ⟨a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,a[7]!,array_eight_eta a⟩
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,hb⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 : U64,
      b=Array.make 8#usize [b0,b1,b2,b3,b4,b5,b6,b7] :=
    ⟨b[0]!,b[1]!,b[2]!,b[3]!,b[4]!,b[5]!,b[6]!,b[7]!,array_eight_eta b⟩
  subst a b
  unfold NativeField.zakura_udon.field.pasta.products.ProductSum.merge mergeExpansion
  simp (config := { maxSteps := 1000000 }) [lift,Array.to_slice_mut,Array.to_slice,core.slice.Slice.iter_mut,
    mutableZipCtor,SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter,
    SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc,Array.from_slice,Slice.setAtNat]
  with_unfolding_all rfl

#print axioms merge_expansion_eq
end UdonVerify.Native
