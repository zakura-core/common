import NativeProductWords

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem product_modulus_upper {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) :
    val4 params.modulus < R / 4 + 2 ^ 126 := by
  have hsmall := params.offset_small
  have hdelta : val4 params.modulus - R / 4 < 2 ^ 126 := by
    by_contra hnot
    have hsquare := Nat.pow_le_pow_left (Nat.le_of_not_lt hnot) 2
    norm_num [B, R] at hsmall hsquare
    omega
  have hpositive := params.offset_positive
  omega

theorem product_three_loose_limit {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) :
    12 * val4 params.modulus ^ 2 < R ^ 2 := by
  have hupper := product_modulus_upper inst params
  have hsquare := Nat.pow_le_pow_left (Nat.le_of_lt hupper) 2
  have hlimit : 12 * (R / 4 + 2 ^ 126) ^ 2 < R ^ 2 := by norm_num [B, R]
  nlinarith only [hsquare, hlimit]

theorem product_double_loose_limit {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) :
    8 * val4 params.modulus ^ 2 < R ^ 2 := by
  nlinarith only [product_three_loose_limit inst params]

theorem product_lt_square_bound (p a b : Nat) (hp : 0 < p) (ha : a < p) (hb : b < p) :
    a * b < p ^ 2 := by
  have hfirst := Nat.mul_le_mul_left a (Nat.le_of_lt hb)
  have hsecond := Nat.mul_lt_mul_of_pos_right ha hp
  simpa only [pow_two] using _root_.lt_of_le_of_lt hfirst hsecond

/-- Restoring a negative wide subtraction cancels exactly its wrapping borrow. -/
theorem product_restoration_math (left product wrapped restored offset borrow carry : Nat)
    (hborrow : borrow ≤ 1) (hcarry : carry ≤ 1)
    (hwrapped : wrapped < R ^ 2) (hrestored : restored < R ^ 2)
    (hleft : left < R * offset) (hproduct : product < R * offset) (hoffset : offset < R)
    (hsub : wrapped + product = left + R ^ 2 * borrow)
    (hadd : restored + R ^ 2 * carry = wrapped + R * offset * borrow) :
    carry = borrow ∧ restored + product = left + R * offset * borrow ∧
      restored < R * offset := by
  have hceq : carry = borrow := by
    have hlimit : R * offset < R ^ 2 := by
      simpa only [pow_two] using Nat.mul_lt_mul_of_pos_left hoffset
        (show 0 < R by norm_num [B, R])
    norm_num [B, R] at hsub hadd hwrapped hrestored hleft hproduct hlimit
    by_cases hz : borrow = 0
    · simp only [hz, mul_zero, add_zero] at hsub hadd
      omega
    · have hone : borrow = 1 := by omega
      simp only [hone, mul_one] at hsub hadd
      omega
  have hexact : restored + product = left + R * offset * borrow := by
    rw [hceq] at hadd
    omega
  refine ⟨hceq, hexact, ?_⟩
  by_cases hz : borrow = 0
  · simp only [hz, mul_zero, add_zero] at hexact
    omega
  · have hone : borrow = 1 := by omega
    simp only [hone, mul_one] at hexact hsub
    omega

#print axioms product_modulus_upper
#print axioms product_three_loose_limit
#print axioms product_double_loose_limit
#print axioms product_lt_square_bound
#print axioms product_restoration_math

end UdonVerify.Native
