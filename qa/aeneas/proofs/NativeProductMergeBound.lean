import NativeProductWords
open Aeneas Std Result
namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The shared and owned right-hand iterator models traverse the same indices. -/
theorem shared_owned_next_eq (it : core.slice.iter.Iter U64) :
    (core.iter.traits.iterator.IteratorSliceIter U64).next it =
    (NativeField.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator U64 8#usize).next it := by rfl

theorem merge_next_eight_none (a b : A8) :
    mutableZipNext (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
      (core.iter.traits.iterator.IteratorSliceIter U64)
      ⟨⟨a.to_slice,8⟩,⟨b.to_slice,8⟩⟩ =
      ok (none,⟨⟨a.to_slice,8⟩,⟨b.to_slice,8⟩⟩,fun z _=>z) := by
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.slice.iter.IteratorIterMut.next,Array.to_slice]

theorem merge_next_some (a b : A8) (index : Nat) (hindex : index<8) :
    ∃ lhs rhs : U64, ∃ back,
    mutableZipNext (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
      (core.iter.traits.iterator.IteratorSliceIter U64)
      ⟨⟨a.to_slice,index⟩,⟨b.to_slice,index⟩⟩ =
      ok (some (lhs,rhs),⟨⟨a.to_slice,index+1⟩,⟨b.to_slice,index+1⟩⟩,back) := by
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,
    Array.to_slice,hindex]


#print axioms shared_owned_next_eq
#print axioms merge_next_eight_none
#print axioms merge_next_some
end UdonVerify.Native
