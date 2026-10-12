import CommonInversionDigitBounds
import CommonInversionBezout

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem active62_low_congruence (a : Signed62) (len : Nat) (hlen : 1 ≤ len ∧ len ≤ 5) :
    Int.ModEq signedRadix (active62Value a len) a[0]!.val := by
  have hcases : len = 1 ∨ len = 2 ∨ len = 3 ∨ len = 4 ∨ len = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold Int.ModEq
    norm_num [active62Value, Finset.sum_range_succ, Int.add_emod, Int.mul_emod, signedRadix]

theorem inversion_row_low_zero (f g : Signed62) (len : Nat) (u v next : Int)
    (hlen : 1 ≤ len ∧ len ≤ 5)
    (hrow : u * active62Value f len + v * active62Value g len = signedRadix * next) :
    fgRowInteger u v f g 0 % signedRadix = 0 := by
  have hlow := ((active62_low_congruence f len hlen).mul_left u).add
    ((active62_low_congruence g len hlen).mul_left v)
  have hzero : Int.ModEq signedRadix (u * active62Value f len + v * active62Value g len) 0 := by
    rw [hrow]
    simp [Int.ModEq, Int.mul_emod]
  exact hlow.symm.trans hzero

theorem inversion_scaled_eq (left right : Int)
    (h : signedRadix * left = signedRadix * right) : left = right := by
  norm_num only [signedRadix] at h
  omega

theorem inversion_all_digit_bounds (before out : Signed62) (len : Nat)
    (hlen : 1 ≤ len ∧ len ≤ 5) (hn : active62Normalized out len)
    (hv : |active62Value out len| ≤ signedRadix ^ len)
    (hinactive : ∀ k : Fin 5, len ≤ k.val → out[k.val]! = before[k.val]!)
    (hbefore : ∀ k : Fin 5, |before[k.val]!.val| ≤ signedRadix) :
    ∀ k : Fin 5, |out[k.val]!.val| ≤ signedRadix := by
  have hactive := active62_digit_bounds_from_value out len hlen hn hv
  intro k
  by_cases hk : k.val < len
  · exact hactive k hk
  · rw [hinactive k (by omega)]
    exact hbefore k

#print axioms active62_low_congruence
#print axioms inversion_row_low_zero
#print axioms inversion_scaled_eq
#print axioms inversion_all_digit_bounds
end UdonVerify.CommonSigned62
