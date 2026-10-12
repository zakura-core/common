import CommonShrinkWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem active62_fold_value (a : Signed62) (len : Nat) (i : Usize) (digit : I64)
    (hlen : 2 ≤ len ∧ len ≤ 5) (hi : i.val = len - 2)
    (hd : digit.val = a[i.val]!.val + signedRadix * a[len - 1]!.val) :
    active62Value (a.set i digit) (len - 1) = active62Value a len := by
  have hcases : len = 2 ∨ len = 3 ∨ len = 4 ∨ len = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hindex : i = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa only [show (0#usize).val = 0 from by decide] using hi
    subst i
    norm_num only [show (0#usize).val = 0 from by decide, Nat.reduceSub] at hd
    norm_num [active62Value, Finset.sum_range_succ, Array.getElem!_Nat_set_ne]
    rw [hd]
    simp only [Array.getElem!_Nat_eq]
    simp
    <;> ring
  · have hindex : i = 1#usize := by
      apply UScalar.eq_of_val_eq
      simpa only [show (1#usize).val = 1 from by decide] using hi
    subst i
    norm_num only [show (1#usize).val = 1 from by decide, Nat.reduceSub] at hd
    norm_num [active62Value, Finset.sum_range_succ, Array.getElem!_Nat_set_ne]
    rw [hd]
    simp only [Array.getElem!_Nat_eq]
    simp
    <;> ring
  · have hindex : i = 2#usize := by
      apply UScalar.eq_of_val_eq
      simpa only [show (2#usize).val = 2 from by decide] using hi
    subst i
    norm_num only [show (2#usize).val = 2 from by decide, Nat.reduceSub] at hd
    norm_num [active62Value, Finset.sum_range_succ, Array.getElem!_Nat_set_ne]
    rw [hd]
    simp only [Array.getElem!_Nat_eq]
    simp
    <;> ring
  · have hindex : i = 3#usize := by
      apply UScalar.eq_of_val_eq
      simpa only [show (3#usize).val = 3 from by decide] using hi
    subst i
    norm_num only [show (3#usize).val = 3 from by decide, Nat.reduceSub] at hd
    norm_num [active62Value, Finset.sum_range_succ, Array.getElem!_Nat_set_ne]
    rw [hd]
    simp only [Array.getElem!_Nat_eq]
    simp
    <;> ring

theorem active62_fold_normalized (a : Signed62) (len : Nat) (i : Usize) (digit : I64)
    (hlen : 2 ≤ len ∧ len ≤ 5) (hi : i.val = len - 2) (hn : active62Normalized a len) :
    active62Normalized (a.set i digit) (len - 1) := by
  intro k hk
  rw [Array.getElem!_Nat_set_ne _ _ _ _ (by rw [hi]; omega)]
  exact hn k (by omega)

theorem active62_fold_bounded (a : Signed62) (len : Nat) (i : Usize) (digit : I64)
    (hlen : 2 ≤ len ∧ len ≤ 5) (hi : i.val = len - 2) (hb : fgInputsBounded len a)
    (hd : |digit.val| ≤ signedRadix) :
    fgInputsBounded (len - 1) (a.set i digit) := by
  intro k hk
  by_cases heq : i.val = k.val
  · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨heq, by have := k.isLt; simpa using k.isLt⟩]
    exact hd
  · rw [Array.getElem!_Nat_set_ne _ _ _ _ heq]
    exact hb k (by omega)

#print axioms active62_fold_value
#print axioms active62_fold_normalized
#print axioms active62_fold_bounded
end UdonVerify.CommonSigned62
