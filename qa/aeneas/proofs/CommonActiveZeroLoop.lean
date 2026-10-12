import CommonActiveZeroMath

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def foldSignedOr (values : List I64) (initial : I64) : I64 :=
  values.foldl (fun a b => a ||| b) initial

theorem fold_signed_or_zero (values : List I64) (initial : I64) :
    foldSignedOr values initial = 0#i64 ↔ initial = 0#i64 ∧ ∀ x ∈ values, x = 0#i64 := by
  induction values generalizing initial with
  | nil => simp [foldSignedOr]
  | cons x xs ih =>
    change foldSignedOr xs (initial ||| x) = 0#i64 ↔ _
    rw [ih, signed_or_eq_zero]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

theorem active_zero_loop_unfold (iter : core.slice.iter.Iter I64) (cond : I64) :
    CommonInvHelpers.field.pasta.safegcd.is_zero_loop iter cond =
      (do let flow ← CommonInvHelpers.field.pasta.safegcd.is_zero_loop.body iter cond
          match flow with
          | .done out => ok out
          | .cont (next, value) => CommonInvHelpers.field.pasta.safegcd.is_zero_loop next value) := by
  unfold CommonInvHelpers.field.pasta.safegcd.is_zero_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont state => rcases state with ⟨next, value⟩; rfl

@[step]
theorem active_zero_loop_spec (iter : core.slice.iter.Iter I64) (cond : I64) :
    CommonInvHelpers.field.pasta.safegcd.is_zero_loop iter cond ⦃ out =>
      out = foldSignedOr (iter.slice.val.drop iter.i) cond ⦄ := by
  generalize hn : iter.slice.val.length - iter.i = n
  induction n using Nat.strong_induction_on generalizing iter cond with
  | h n ih =>
    rw [active_zero_loop_unfold]
    unfold CommonInvHelpers.field.pasta.safegcd.is_zero_loop.body
      core.slice.iter.IteratorSliceIter.next
    by_cases hlt : iter.i < iter.slice.len
    · simp only [dif_pos hlt, bind_ok, Std.uncurry_apply_pair, Std.uncurry,
        CommonInvHelpers.I64.Insts.CoreOpsBitBitOrAssignShared0I64.bitor_assign]
      have hlength : iter.i < iter.slice.val.length := hlt
      have hdrop := List.drop_eq_getElem_cons hlength
      change CommonInvHelpers.field.pasta.safegcd.is_zero_loop
        {iter with i := iter.i + 1} (cond ||| iter.slice[iter.i])
        ⦃ out => out = foldSignedOr (iter.slice.val.drop iter.i) cond ⦄
      rw [hdrop]
      exact ih (iter.slice.val.length - (iter.i + 1)) (by omega)
        {iter with i := iter.i + 1} (cond ||| iter.slice[iter.i]) rfl
    · simp only [dif_neg hlt, bind_ok, Std.uncurry_apply_pair, Std.uncurry, WP.spec_ok]
      have hdrop : iter.slice.val.drop iter.i = [] :=
        List.drop_eq_nil_of_le (by change ¬iter.i < iter.slice.val.length at hlt; omega)
      rw [hdrop]
      rfl

#print axioms fold_signed_or_zero
#print axioms active_zero_loop_unfold
#print axioms active_zero_loop_spec
end UdonVerify.CommonSigned62
