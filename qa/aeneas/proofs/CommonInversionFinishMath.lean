import CommonInversionInvariant

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem signed62_255_top_bound (a : Signed62) (hn : signed62Normalized a)
    (hv : 0 ≤ signed62Value a ∧ signed62Value a < 2 ^ 255) :
    0 ≤ a[4]!.val ∧ a[4]!.val < 128 := by
  have hprefix := active62_low_bound a hn 4 (by decide)
  have hsum := active62_succ a 4
  rw [active62_value_five] at hsum
  norm_num only [signedRadix] at hprefix hsum hv ⊢
  constructor <;> omega

theorem inversion_normalized_bezout (modulus x scale f d out : Int) (negative : Prop) [Decidable negative]
    (hunit : f = 1 ∨ f = -1) (hsign : negative ↔ f < 0)
    (hd : Int.ModEq modulus (x * d) (scale * f))
    (hn : Int.ModEq modulus out (if negative then -d else d)) :
    Int.ModEq modulus (x * out) scale := by
  rcases hunit with hpos | hneg
  · have hnot : ¬negative := by rw [hsign, hpos]; decide
    rw [if_neg hnot] at hn
    rw [hpos, mul_one] at hd
    exact (hn.mul_left x).trans hd
  · have hyes : negative := by rw [hsign, hneg]; decide
    rw [if_pos hyes] at hn
    rw [hneg, mul_neg_one] at hd
    have hnegD : Int.ModEq modulus (x * -d) scale := by
      simpa only [neg_neg, mul_neg] using hd.neg
    exact (hn.mul_left x).trans hnegD

#print axioms signed62_255_top_bound
#print axioms inversion_normalized_bezout
end UdonVerify.CommonSigned62
