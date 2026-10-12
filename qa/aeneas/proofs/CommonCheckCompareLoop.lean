import CommonCheckCompareControl

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem check_compare_loop_spec (a b : Signed62) (ha : signed62Normalized a)
    (hb : signed62Normalized b) (endIndex : Usize) (he : endIndex.val ≤ 5)
    (heq : ∀ j : Fin 5, endIndex.val ≤ j.val → a[j.val]!.val = b[j.val]!.val) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop1 (checkRev endIndex) a b
      ⦃ out => CheckCompareResult a b out ⦄ := by
  generalize hcount : endIndex.val = count
  induction count using Nat.strong_induction_on generalizing endIndex with
  | h count ih =>
    rw [check_compare_loop_unfold]
    unfold CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop1.body
    by_cases hz : count = 0
    · have heqZero : endIndex = 0#usize := by
        apply UScalar.eq_of_val_eq
        change endIndex.val = 0
        omega
      subst endIndex
      rw [check_rev_next_none]
      simp only [bind_ok, Std.uncurry_apply_pair, WP.spec_ok]
      exact signed62_equal_of_digits a b (by intro j; exact heq j (by change 0 ≤ j.val; omega))
    · have hpositive : 0 < endIndex.val := by omega
      let previous : Usize := UScalar.ofNatCore (endIndex.val - 1)
        (by have := endIndex.hBounds; omega)
      have hprevious : previous.val = endIndex.val - 1 := UScalar.ofNatCore_val_eq _
      have hp5 : previous.val < 5 := by omega
      rw [check_rev_next_some endIndex previous hpositive hprevious]
      simp only [bind_ok, Std.uncurry_apply_pair]
      rw [fg_index_eq a previous hp5, bind_ok, fg_index_eq b previous hp5, bind_ok]
      have hhigher : ∀ j : Fin 5, previous.val < j.val → a[j.val]!.val = b[j.val]!.val := by
        intro j hj
        exact heq j (by omega)
      by_cases hlt : a[previous.val]! < b[previous.val]!
      · simp only [if_pos hlt, bind_ok, WP.spec_ok]
        exact signed62_lt_of_high_digit a b ha hb ⟨previous.val, hp5⟩ hhigher (by scalar_tac)
      · by_cases hgt : a[previous.val]! > b[previous.val]!
        · simp only [if_neg hlt, if_pos hgt, bind_ok, WP.spec_ok]
          exact signed62_lt_of_high_digit b a hb ha ⟨previous.val, hp5⟩
            (by intro j hj; exact (hhigher j hj).symm) (by scalar_tac)
        · simp only [if_neg hlt, if_neg hgt, bind_ok, Std.uncurry_apply_pair]
          have hequal : a[previous.val]!.val = b[previous.val]!.val := by scalar_tac
          have heqNext : ∀ j : Fin 5, previous.val ≤ j.val → a[j.val]!.val = b[j.val]!.val := by
            intro j hj
            by_cases hjEq : j.val = previous.val
            · simpa only [hjEq] using hequal
            · exact heq j (by omega)
          exact ih previous.val (by omega) previous (by omega) heqNext rfl

#print axioms check_compare_loop_spec
end UdonVerify.CommonSigned62
