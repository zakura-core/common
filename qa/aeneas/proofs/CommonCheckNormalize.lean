import CommonCheckMul

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem signed62_low_shift_eq (value : I64) (h : 0 ≤ value.val ∧ value.val < signedRadix) :
    value >>> 62#i32 = ok 0#i64 := by
  apply fg_result_eq
  step -grind with I64.ShiftRight_IScalar_spec as ⟨out, hval, _⟩
  apply IScalar.eq_of_val_eq
  have hv : out.val = value.val / signedRadix := by
    simpa only [show (62#i32).toNat = 62 from by decide, Int.shiftRight_eq_div_pow,
      signedRadix, Nat.cast_pow, Nat.cast_ofNat] using hval
  rw [hv]
  change value.val / signedRadix = 0
  norm_num only [signedRadix] at h ⊢
  omega

theorem check_normalize_loop_unfold (iter : core.ops.range.Range Usize) (a b : Signed62) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop0 iter a b =
      (do let flow ← CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop0.body iter a b
          match flow with
          | .done result => ok result
          | .cont (next, a1, b1) =>
            CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop0 next a1 b1) := by
  unfold CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop0
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done result => rfl
  | cont state => rcases state with ⟨next, a1, b1⟩; rfl

@[step]
theorem check_normalize_loop_spec (a b : Signed62) (ha : signed62Normalized a)
    (hb : signed62Normalized b) (iter : core.ops.range.Range Usize)
    (hstart : iter.start.val ≤ 4) (hend : iter.end = 4#usize) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop0 iter a b
      ⦃ result => result = (a, b) ⦄ := by
  generalize hn : 4 - iter.start.val = n
  induction n using Nat.strong_induction_on generalizing iter with
  | h n ih =>
    rw [check_normalize_loop_unfold]
    unfold CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop0.body
    by_cases hlt : iter.start.val < iter.end.val
    · obtain ⟨⟨item, next⟩, hnext, hitem, hnextStart, hnextEnd⟩ :=
        WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec iter hlt)
      subst item
      have hi : iter.start.val < 4 := by rw [hend] at hlt; exact hlt
      rw [hnext]
      simp only [bind_ok, Std.uncurry_apply_pair]
      rw [fg_index_eq a iter.start (by omega), bind_ok,
        signed62_low_shift_eq _ (ha ⟨iter.start.val, hi⟩), bind_ok]
      simp only [massert, bind_ok, ite_true]
      rw [fg_index_eq b iter.start (by omega), bind_ok,
        signed62_low_shift_eq _ (hb ⟨iter.start.val, hi⟩), bind_ok]
      simp only [massert, bind_ok, ite_true, Std.uncurry_apply_pair]
      exact ih (4 - next.start.val) (by rw [hnextStart]; omega) next
        (by rw [hnextStart]; omega) (by rw [hnextEnd, hend]) rfl
    · obtain ⟨⟨item, next⟩, hnext, hitem, hnextEq⟩ :=
        WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec iter (by omega))
      subst item
      subst next
      rw [hnext]
      simp only [bind_ok, Std.uncurry_apply_pair, WP.spec_ok]

#print axioms signed62_low_shift_eq
#print axioms check_normalize_loop_unfold
#print axioms check_normalize_loop_spec
end UdonVerify.CommonSigned62
