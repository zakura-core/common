import NativeLargePieces

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem large_append_spec (low digit : U32) (count : I32)
    (hcount : count.val = 8 ∨ count.val = 16 ∨ count.val = 24)
    (hlow : low.val < 2 ^ count.val.toNat) (hdigit : digit.val < 256) :
    largeAppend low digit count ⦃ out =>
      out.val = low.val + 2 ^ count.val.toNat * digit.val ∧
      out.val < 2 ^ (count.val.toNat + 8) ⦄ := by
  exact Native.large_byte_append_spec low digit count hcount hlow hdigit

@[step]
theorem large_low_index_spec (value : U32) :
    largeLowIndex value ⦃ out => out.val = value.val % 256 ∧ out.val < 256 ⦄ := by
  simp only [largeLowIndex, lift, WP.spec_ok, U32.cast_Usize_val_eq, Native.large_mask_byte]
  exact ⟨trivial, Nat.mod_lt _ (by decide)⟩

@[step]
theorem large_top_index_spec (value : U32) (count : I32)
    (hcount : count.val = 8 ∨ count.val = 16 ∨ count.val = 24) :
    largeTopIndex value count ⦃ out => out.val = value.val / 2 ^ count.val.toNat ⦄ := by
  unfold largeTopIndex
  step +scalarTac -grind with U32.ShiftRight_IScalar_spec as ⟨shifted, hshifted, hbound⟩
  simpa only [lift, WP.spec_ok, U32.cast_Usize_val_eq, Nat.shiftRight_eq_div_pow] using hshifted

@[step]
theorem large_digit_index_spec (value : U32) (count : I32)
    (hcount : count.val = 8 ∨ count.val = 16 ∨ count.val = 24) :
    largeDigitIndex value count ⦃ out =>
      out.val = value.val / 2 ^ count.val.toNat % 256 ∧ out.val < 256 ⦄ := by
  unfold largeDigitIndex
  step +scalarTac -grind with U32.ShiftRight_IScalar_spec as ⟨shifted, hshifted, hbound⟩
  have hvalue : shifted.val = value.val / 2 ^ count.val.toNat := by
    simpa only [Nat.shiftRight_eq_div_pow] using hshifted
  simp only [lift, WP.spec_ok, U32.cast_Usize_val_eq, Native.large_mask_byte, hvalue]
  exact ⟨trivial, Nat.mod_lt _ (by decide)⟩

#print axioms large_append_spec
#print axioms large_low_index_spec
#print axioms large_top_index_spec
#print axioms large_digit_index_spec

end UdonVerify.LargeNativeBridge
