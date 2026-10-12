import CommonFG62One
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem fg_result_eq {α : Type} {result : Result α} {value : α}
    (h : result ⦃ out => out = value ⦄) : result = ok value := by
  cases h
  simp_all

theorem fg_usize_sub_eq (a b out : Usize) (hle : b.val ≤ a.val)
    (hvalue : a.val - b.val = out.val) : a - b = ok out := by
  apply fg_result_eq
  step +scalarTac -grind as ⟨result, hresult⟩
  apply UScalar.eq_of_val_eq
  omega

theorem fg_next_some_eq (range : core.ops.range.Range Usize) (next : Usize)
    (hlt : range.start.val < range.end.val) (hnext : next.val = range.start.val + 1) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range =
      ok (some range.start, { start := next, «end» := range.end }) := by
  apply fg_result_eq
  step -grind with (core.iter.range.IteratorRange.next_Usize_some_spec range hlt)
    as ⟨pair, hout, hstart, hend⟩
  rcases pair with ⟨out, updated⟩
  dsimp only at hout hstart hend
  have hs : updated.start = next := UScalar.eq_of_val_eq (hstart.trans hnext.symm)
  have hr : updated = { start := next, «end» := range.end } := by
    cases updated
    simp_all
  exact Prod.ext hout hr

theorem fg_next_none_eq (range : core.ops.range.Range Usize)
    (hge : range.end.val ≤ range.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range = ok (none, range) := by
  apply fg_result_eq
  step -grind with (core.iter.range.IteratorRange.next_Usize_none_spec range hge)
    as ⟨out, hout, hupdated⟩
  exact Prod.ext hout hupdated

theorem fg_index_eq (a : Signed62) (i : Usize) (hi : i.val < 5) :
    Array.index_usize a i = ok a[i.val]! := by
  have hbound : i.val < a.val.length := by simpa using hi
  rw [Array.index_usize, Array.getElem?_Usize_eq, List.getElem?_eq_getElem hbound]
  rw [Array.getElem!_Nat_eq, getElem!_pos a.val i.val hbound]

theorem fg_index_mut_eq (a : Signed62) (i : Usize) (hi : i.val < 5) :
    Array.index_mut_usize a i = ok (a[i.val]!, a.set i) := by
  simp only [Array.index_mut_usize, Bind.bind, fg_index_eq a i hi, bind_ok]

theorem fg_update_eq (a : Signed62) (i : Usize) (x : I64) (hi : i.val < 5) :
    Array.update a i x = ok (a.set i x) := by
  have hbound : i.val < a.val.length := by simpa using hi
  rw [Array.update, Array.getElem?_Usize_eq, List.getElem?_eq_getElem hbound]
  rfl

theorem fg_mask_eq :
    CommonFG62.field.pasta.safegcd.MASK62 = ok 4611686018427387903#u64 := by
  have h : CommonFG62.field.pasta.safegcd.MASK62 =
      Signed62Native.field.pasta.safegcd.MASK62 := by
    unfold CommonFG62.field.pasta.safegcd.MASK62 Signed62Native.field.pasta.safegcd.MASK62
    rfl
  exact h.trans mask62_eq

#print axioms fg_index_eq
#print axioms fg_index_mut_eq
#print axioms fg_update_eq
#print axioms fg_mask_eq
#print axioms fg_result_eq
#print axioms fg_usize_sub_eq
#print axioms fg_next_some_eq
#print axioms fg_next_none_eq
end UdonVerify.CommonSigned62
