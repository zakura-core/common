import CommonCheckMulKernel
import CommonFG62Value

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem check_mul_select_spec (a : Signed62) (alen index : Usize) (factor : I64) (carry : I128)
    (hi : index.val < 5) (hc : |carry.val| ≤ 3) (hf : |factor.val| ≤ 2)
    (ha : |a[index.val]!.val| ≤ signedRadix) :
    (if index < alen then do
      let digit ← Array.index_usize a index
      checkMulAccumulate carry digit factor
      else ok carry) ⦃ out =>
        out.val = carry.val + (if index.val < alen.val then a[index.val]!.val * factor.val else 0) ∧
        |out.val| ≤ 2 * signedRadix + 3 ⦄ := by
  by_cases hltVal : index.val < alen.val
  · have hlt : index < alen := by scalar_tac
    rw [if_pos hlt]
    rw [fg_index_eq a index hi]
    simp only [bind_ok, if_pos hltVal]
    exact check_mul_accumulate_spec carry a[index.val]! factor hc ha hf
  · have hnlt : ¬ index < alen := by scalar_tac
    rw [if_neg hnlt]
    simp only [WP.spec_ok, if_neg hltVal, add_zero, true_and]
    have hb : 0 < signedRadix := by norm_num [signedRadix]
    omega

@[step]
theorem check_mul_round_spec (a : Signed62) (alen : Usize) (factor : I64)
    (index : Usize) (carry : I128) (out : Signed62)
    (hi : index.val < 5) (hc : |carry.val| ≤ 3) (hf : |factor.val| ≤ 2)
    (ha : |a[index.val]!.val| ≤ signedRadix) :
    checkMulRound a alen factor index carry out ⦃ result =>
      ∃ acc : I128,
        acc.val = carry.val + (if index.val < alen.val then a[index.val]!.val * factor.val else 0) ∧
        result.1 = a ∧ result.2.1.val = acc.val / signedRadix ∧
        |result.2.1.val| ≤ 3 ∧ result.2.2 = out.set index (fgRowDigit acc) ⦄ := by
  unfold checkMulRound
  apply WP.spec_bind (check_mul_select_spec a alen index factor carry hi hc hf ha)
  intro acc hacc
  rw [inv_helpers_mask_eq]
  simp only [bind_ok]
  rw [fg_update_eq out index _ hi]
  simp only [bind_ok]
  step -grind with (check_mul_shift_spec acc hacc.2) as ⟨nextCarry, hnextCarry, hbound⟩
  try simp only [WP.spec_ok]
  refine ⟨acc, hacc.1, ?_⟩
  simpa only [fgRowDigit, true_and, and_true] using And.intro hnextCarry hbound

theorem active62_succ (a : Signed62) (k : Nat) :
    active62Value a (k + 1) = active62Value a k + signedRadix ^ k * a[k]!.val := by
  exact Finset.sum_range_succ _ k

theorem active62_set_prefix (a : Signed62) (index : Usize) (value : I64) :
    active62Value (a.set index value) index.val = active62Value a index.val := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [Array.getElem!_Nat_set_ne _ _ _ _ (by have := Finset.mem_range.mp hk; omega)]

theorem active62_set_succ (a : Signed62) (index : Usize) (value : I64) (hi : index.val < 5) :
    active62Value (a.set index value) (index.val + 1) =
      active62Value a index.val + signedRadix ^ index.val * value.val := by
  rw [active62_succ, active62_set_prefix,
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hi⟩]

theorem active62_min_succ (a : Signed62) (len k : Nat) :
    active62Value a (min (k + 1) len) = active62Value a (min k len) +
      (if k < len then signedRadix ^ k * a[k]!.val else 0) := by
  by_cases hk : k < len
  · rw [Nat.min_eq_left (by omega : k + 1 ≤ len), Nat.min_eq_left (by omega : k ≤ len),
      if_pos hk, active62_succ]
  · rw [Nat.min_eq_right (by omega : len ≤ k + 1), Nat.min_eq_right (by omega : len ≤ k),
      if_neg hk, add_zero]

#print axioms check_mul_select_spec
#print axioms check_mul_round_spec
#print axioms active62_succ
#print axioms active62_set_prefix
#print axioms active62_set_succ
#print axioms active62_min_succ
end UdonVerify.CommonSigned62
