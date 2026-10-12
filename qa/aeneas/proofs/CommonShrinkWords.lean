import CommonNormalizeWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem signed_xor_eq_zero (a b : I64) : a ^^^ b = 0#i64 ↔ a = b := by
  constructor
  · intro h
    have hb := congrArg IScalar.bv h
    change a.bv ^^^ b.bv = 0#64 at hb
    exact I64.bv_eq_imp_eq a b (BitVec.xor_eq_zero_iff.mp hb)
  · rintro rfl
    apply I64.bv_eq_imp_eq
    change a.bv ^^^ a.bv = 0#64
    simp

theorem shrink_sign_extension_iff (value : I64) :
    value ^^^ signMask value = 0#i64 ↔ value = 0#i64 ∨ value = (-1)#i64 := by
  rw [signed_xor_eq_zero]
  unfold signMask
  split_ifs with hnegative
  · constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · subst value; contradiction
      · exact h
  · constructor
    · intro h; exact Or.inl h
    · rintro (h | h)
      · exact h
      · subst value; contradiction

def shrinkDigit (low top : I64) : Result I64 := do
  let shifted ← IScalar.hcast .U64 top <<< 62#i32
  ok (UScalar.hcast .I64 (IScalar.hcast .U64 low ||| shifted))

@[step]
theorem shrink_digit_spec (low top : I64)
    (hl : 0 ≤ low.val ∧ low.val < signedRadix)
    (ht : top = 0#i64 ∨ top = (-1)#i64) :
    shrinkDigit low top ⦃ out => out.val = low.val + signedRadix * top.val ∧
      |out.val| ≤ signedRadix ⦄ := by
  have hcast : ((IScalar.hcast .U64 low).val : Int) = low.val := by
    rw [IScalar.hcast_val_eq]
    change ((low.val % 18446744073709551616).toNat : Int) = low.val
    rw [Int.emod_eq_of_lt hl.1 (by norm_num only [signedRadix] at hl; omega), Int.toNat_of_nonneg hl.1]
  have hlow : (IScalar.hcast .U64 low).val < 2 ^ 62 := by
    norm_num only [signedRadix] at hl
    omega
  have hv : |low.val + signedRadix * top.val| ≤ signedRadix := by
    rcases ht with rfl | rfl <;> rw [abs_le] <;> norm_num only [signedRadix, show (0#i64).val = 0 from by decide,
      show ((-1)#i64).val = -1 from by decide] at hl ⊢ <;>
      constructor <;> omega
  unfold shrinkDigit
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shifted, hshift, _⟩
  have hword : Int.ModEq (2 ^ 64) ((IScalar.hcast .U64 low ||| shifted).val : Int)
      (low.val + signedRadix * top.val) := by
    rcases ht with rfl | rfl
    · have hz : shifted = 0#u64 := by
        apply UScalar.eq_of_val_eq
        norm_num [show IScalar.hcast .U64 0#i64 = 0#u64 from by decide,
          U64.size, U64.numBits, UScalar.size, UScalarTy.numBits, show (62#i32).toNat = 62 from by decide,
          Nat.shiftLeft_eq] at hshift ⊢
        exact hshift
      rw [hz]
      simp only [UScalar.val_or, show (0#u64).val = 0 from by decide, Nat.or_zero, hcast]
      simp [Int.ModEq]
    · have hs : shifted.val = 3 * 2 ^ 62 := by
        norm_num [show IScalar.hcast .U64 (-1)#i64 = 18446744073709551615#u64 from by decide,
          U64.size, U64.numBits, UScalar.size, UScalarTy.numBits, show (62#i32).toNat = 62 from by decide,
          Nat.shiftLeft_eq] at hshift ⊢
        exact hshift
      have hor : (IScalar.hcast .U64 low).val ||| (3 * 2 ^ 62) =
          3 * 2 ^ 62 + (IScalar.hcast .U64 low).val := by
        rw [Nat.or_comm]
        simpa only [mul_comm] using (Nat.two_pow_add_eq_or_of_lt hlow (a := 3)).symm
      simp only [UScalar.val_or, hs, hor, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, hcast]
      norm_num only [signedRadix, Int.ModEq, show ((-1)#i64).val = -1 from by decide]
      omega
  try simp only [WP.spec_ok]
  exact ⟨word_signed_value _ _ hv hword, by rw [word_signed_value _ _ hv hword]; exact hv⟩

#print axioms signed_xor_eq_zero
#print axioms shrink_sign_extension_iff
#print axioms shrink_digit_spec
end UdonVerify.CommonSigned62
