import SqrtCorrectionMath
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace UdonVerify.LargeSqrt
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem digit_prefix (exponent : Nat) (digit : Fin 4) :
    exponent % 256 ^ (digit.val + 1) = exponent % 256 ^ digit.val +
      256 ^ digit.val * (exponent / 256 ^ digit.val % 256) := by
  fin_cases digit <;> norm_num <;> omega

theorem corrected_exponent_mod (exponent : Nat) (digit : Fin 4) :
    Nat.ModEq (256 ^ 4)
      ((exponent % 256 ^ digit.val) * 256 ^ (3 - digit.val) +
        (exponent / 256 ^ digit.val % 256) * 256 ^ 3)
      (exponent * 256 ^ (3 - digit.val)) := by
  have hprefix := digit_prefix exponent digit
  have hdecompose := Nat.mod_add_div exponent (256 ^ (digit.val + 1))
  unfold Nat.ModEq
  fin_cases digit <;> norm_num at hprefix hdecompose ⊢ <;> omega

theorem four_bytes (exponent : Nat) (hbound : exponent < 256 ^ 4) :
    exponent = exponent % 256 + 256 * (exponent / 256 % 256) +
      256 ^ 2 * (exponent / 256 ^ 2 % 256) +
      256 ^ 3 * (exponent / 256 ^ 3 % 256) := by
  have h0 := digit_prefix exponent ⟨0, by decide⟩
  have h1 := digit_prefix exponent ⟨1, by decide⟩
  have h2 := digit_prefix exponent ⟨2, by decide⟩
  have h3 := digit_prefix exponent ⟨3, by decide⟩
  norm_num at h0 h1 h2 h3 hbound ⊢
  omega

theorem rounded_half (exponent : Nat) (hbound : exponent < 2 ^ 32) :
    (exponent + 1) / 2 ≤ 2 ^ 31 ∧
      2 * ((exponent + 1) / 2) = exponent + exponent % 2 := by
  norm_num at hbound ⊢
  omega

theorem rounded_top_byte (exponent : Nat) (hbound : exponent < 2 ^ 32) :
    ((exponent + 1) / 2) / 256 ^ 3 ≤ 128 := by
  have h := (rounded_half exponent hbound).1
  norm_num at h ⊢
  omega

theorem inverse_exponent_exists {K : Type*} [Field K] (root t : K)
    (hroot : IsPrimitiveRoot root (256 ^ 4)) (ht : t ^ (256 ^ 4) = 1) :
    ∃ exponent < 256 ^ 4, t * root ^ exponent = 1 := by
  letI : NeZero (256 ^ 4) := ⟨by decide⟩
  obtain ⟨index, hindex, hvalue⟩ := hroot.eq_pow_of_pow_eq_one ht
  by_cases hz : index = 0
  · refine ⟨0, by decide, ?_⟩
    simpa only [hz, pow_zero, mul_one] using hvalue.symm
  · refine ⟨256 ^ 4 - index, by omega, ?_⟩
    rw [← hvalue, ← pow_add, Nat.add_sub_of_le (by omega : index ≤ 256 ^ 4)]
    exact hroot.pow_eq_one

theorem inverse_byte_complement (exponent : Nat) (hbound : exponent < 256) :
    (256 - ((256 - exponent) % 256)) % 256 = exponent := by
  omega

theorem subgroup_complement_power {K : Type*} [CommMonoid K] (root : K)
    (hroot : root ^ (256 ^ 4) = 1) (exponent : Nat) (hbound : exponent < 256) :
    root ^ (exponent * 256 ^ 3) * root ^ (((256 - exponent) % 256) * 256 ^ 3) = 1 := by
  by_cases hz : exponent = 0
  · simp [hz]
  · have hlow : 256 - exponent < 256 := by omega
    rw [Nat.mod_eq_of_lt hlow, ← pow_add]
    have hsum : exponent * 256 ^ 3 + (256 - exponent) * 256 ^ 3 = 256 ^ 4 := by
      norm_num at hbound ⊢
      omega
    rw [hsum]
    exact hroot

theorem subgroup_inverse_value {K : Type*} [CommMonoid K] (root alpha : K)
    (hroot : root ^ (256 ^ 4) = 1) (exponent : Nat) (hbound : exponent < 256)
    (hinverse : alpha * root ^ (exponent * 256 ^ 3) = 1) :
    alpha = root ^ (((256 - exponent) % 256) * 256 ^ 3) := by
  calc
    alpha = alpha * 1 := by rw [mul_one]
    _ = alpha * (root ^ (exponent * 256 ^ 3) *
        root ^ (((256 - exponent) % 256) * 256 ^ 3)) := by
      rw [subgroup_complement_power root hroot exponent hbound]
    _ = (alpha * root ^ (exponent * 256 ^ 3)) *
        root ^ (((256 - exponent) % 256) * 256 ^ 3) := by rw [mul_assoc]
    _ = root ^ (((256 - exponent) % 256) * 256 ^ 3) := by rw [hinverse, one_mul]

/-- Each corrected lookup argument has the inverse exponent given by the next byte. -/
theorem corrected_lookup {K : Type*} [CommMonoid K] (root t : K) (exponent : Nat)
    (hroot : root ^ (256 ^ 4) = 1) (hinverse : t * root ^ exponent = 1) (digit : Fin 4) :
    (t ^ (256 ^ (3 - digit.val)) *
      root ^ ((exponent % 256 ^ digit.val) * 256 ^ (3 - digit.val))) *
        root ^ ((exponent / 256 ^ digit.val % 256) * 256 ^ 3) = 1 := by
  rw [mul_assoc, ← pow_add,
    pow_eq_pow_of_modEq (corrected_exponent_mod exponent digit) hroot,
    pow_mul, ← mul_pow, hinverse, one_pow]

/-- Rounding an odd inverse exponent returns a root of the alternate nonsquare multiple. -/
theorem candidate_square {K : Type*} [CommRing K] (a t x root : K) (exponent : Nat)
    (hbound : exponent < 2 ^ 32) (hsquare : x ^ 2 = a * t)
    (hinverse : t * root ^ exponent = 1) :
    (x * root ^ ((exponent + 1) / 2)) ^ 2 = a * root ^ (exponent % 2) := by
  rw [mul_pow, hsquare, ← pow_mul]
  have hhalf := (rounded_half exponent hbound).2
  rw [show ((exponent + 1) / 2) * 2 = exponent + exponent % 2 by omega, pow_add]
  calc
    (a * t) * (root ^ exponent * root ^ (exponent % 2)) =
      a * (t * root ^ exponent) * root ^ (exponent % 2) := by ring
    _ = a * root ^ (exponent % 2) := by rw [hinverse, mul_one]

#print axioms digit_prefix
#print axioms corrected_exponent_mod
#print axioms four_bytes
#print axioms rounded_half
#print axioms rounded_top_byte
#print axioms inverse_exponent_exists
#print axioms inverse_byte_complement
#print axioms subgroup_complement_power
#print axioms subgroup_inverse_value
#print axioms corrected_lookup
#print axioms candidate_square

end UdonVerify.LargeSqrt
