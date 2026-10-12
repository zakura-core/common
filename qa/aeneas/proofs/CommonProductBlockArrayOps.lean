import CommonProductBlockPrimitives

open Aeneas Std Result
namespace UdonVerify.ProductBlock
set_option maxHeartbeats 1000000

/-- Fixed in-bounds reads retain their original checked-array semantics. -/
theorem block_index_eq {α : Type} [Inhabited α] {N : Usize}
    (a : Array α N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = ok a[i.val]! := by
  have hbound : i.val < a.val.length := by simpa using hi
  rw [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem hbound]
  rw [Array.getElem!_Nat_eq,getElem!_pos a.val i.val hbound]

theorem block_update_eq {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (x : α) (hi : i.val < N.val) :
    Array.update a i x = ok (a.set i x) := by
  have hbound : i.val < a.val.length := by simpa using hi
  rw [Array.update,Array.getElem?_Usize_eq,List.getElem?_eq_getElem hbound]
  rfl

#print axioms block_index_eq
#print axioms block_update_eq
end UdonVerify.ProductBlock
