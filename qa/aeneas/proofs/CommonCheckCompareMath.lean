import CommonCheckMul

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem active62_low_bound (a : Signed62) (hn : signed62Normalized a) (k : Nat) (hk : k ≤ 4) :
    0 ≤ active62Value a k ∧ active62Value a k < signedRadix ^ k := by
  induction k with
  | zero => simp [active62Value]
  | succ k ih =>
    have hprevious := ih (by omega)
    have hd := hn ⟨k, by omega⟩
    have hp : 0 < signedRadix ^ k := pow_pos (by norm_num [signedRadix]) _
    rw [active62_succ, pow_succ]
    constructor <;> nlinarith

theorem active62_high_equal (a b : Signed62) (k : Nat) (hk : k ≤ 5)
    (heq : ∀ j : Fin 5, k ≤ j.val → a[j.val]!.val = b[j.val]!.val) :
    signed62Value a - signed62Value b = active62Value a k - active62Value b k := by
  rw [← active62_value_five a, ← active62_value_five b]
  have hsum : k + (5 - k) = 5 := by omega
  have ha : active62Value a 5 = active62Value a k +
      ∑ j ∈ Finset.range (5 - k), signedRadix ^ (k + j) * a[k + j]!.val := by
    simpa only [active62Value, hsum] using
      (Finset.sum_range_add (fun j => signedRadix ^ j * a[j]!.val) k (5 - k))
  have hb : active62Value b 5 = active62Value b k +
      ∑ j ∈ Finset.range (5 - k), signedRadix ^ (k + j) * b[k + j]!.val := by
    simpa only [active62Value, hsum] using
      (Finset.sum_range_add (fun j => signedRadix ^ j * b[j]!.val) k (5 - k))
  have htail : (∑ j ∈ Finset.range (5 - k), signedRadix ^ (k + j) * a[k + j]!.val) =
      ∑ j ∈ Finset.range (5 - k), signedRadix ^ (k + j) * b[k + j]!.val := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    rw [heq ⟨k + j, by omega⟩ (by dsimp; omega)]
  rw [ha, hb, htail]
  ring

theorem signed62_lt_of_high_digit (a b : Signed62) (ha : signed62Normalized a)
    (hb : signed62Normalized b) (k : Fin 5)
    (heq : ∀ j : Fin 5, k.val < j.val → a[j.val]!.val = b[j.val]!.val)
    (hlt : a[k.val]!.val < b[k.val]!.val) : signed62Value a < signed62Value b := by
  have hlowA := active62_low_bound a ha k.val (by have := k.isLt; omega)
  have hlowB := active62_low_bound b hb k.val (by have := k.isLt; omega)
  have he := active62_high_equal a b (k.val + 1) (by have := k.isLt; omega)
    (by intro j hj; exact heq j (by omega))
  rw [active62_succ, active62_succ] at he
  have hp : 0 < signedRadix ^ k.val := pow_pos (by norm_num [signedRadix]) _
  nlinarith

theorem signed62_equal_of_digits (a b : Signed62)
    (heq : ∀ j : Fin 5, a[j.val]!.val = b[j.val]!.val) : signed62Value a = signed62Value b := by
  have h := active62_high_equal a b 0 (by decide) (by intro j _; exact heq j)
  simp only [active62Value, Finset.range_zero, Finset.sum_empty] at h
  omega

def CheckCompareResult (a b : Signed62) : Ordering → Prop
  | .lt => signed62Value a < signed62Value b
  | .eq => signed62Value a = signed62Value b
  | .gt => signed62Value b < signed62Value a

#print axioms active62_low_bound
#print axioms active62_high_equal
#print axioms signed62_lt_of_high_digit
#print axioms signed62_equal_of_digits
end UdonVerify.CommonSigned62
