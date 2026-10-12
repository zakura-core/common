import NativeLargeTableMath

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 10000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem large_low_word (limbs : A4) : limbs[0]!.val % 2 ^ 32 = val4 limbs % 2 ^ 32 := by
  simp [val4, Nat.add_mod, Nat.mul_mod, B]

theorem large_mask_byte (value : U32) : (value &&& 255#u32).val = value.val % 256 := by
  rw [UScalar.val_and]
  simpa using Nat.and_two_pow_sub_one_eq_mod value.val 8

theorem large_mask_parity (value : U32) : (value &&& 1#u32).val = value.val % 2 := by
  rw [UScalar.val_and]
  simpa using Nat.and_two_pow_sub_one_eq_mod value.val 1

@[step]
theorem large_hash_spec (key multiplier : U32) :
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.hash key multiplier
      ⦃ out => out.val = largeHash key.val multiplier.val ∧ out.val < 1024 ⦄ := by
  unfold LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.hash
  simp only [lift, bind_ok]
  step -grind with U32.ShiftRight_IScalar_spec as ⟨shifted, hshifted, hbound⟩
  simp only [WP.spec_ok, U32.cast_Usize_val_eq]
  have hvalue : shifted.val = largeHash key.val multiplier.val := by
    simpa [largeHash, Nat.shiftRight_eq_div_pow, core.num.U32.wrapping_mul_val_eq,
      U32.size, U32.numBits] using hshifted
  rw [hvalue]
  refine ⟨rfl, ?_⟩
  have hmod := Nat.mod_lt (key.val * multiplier.val) (by norm_num : 0 < 2 ^ 32)
  unfold largeHash
  norm_num at hmod ⊢
  omega

@[step]
theorem large_half_exponent_spec (exponent : U32) :
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.half_exponent exponent
      ⦃ out => out.val = (exponent.val + 1) / 2 ∧ out.val ≤ 2 ^ 31 ⦄ := by
  have hwiden : (UScalar.cast .U64 exponent).val = exponent.val := U32.cast_U64_val_eq exponent
  have hexponent : exponent.val < 2 ^ 32 := by scalar_tac
  unfold LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.half_exponent
  simp only [lift, bind_ok]
  step +scalarTac -grind with U64.add_spec as ⟨added, hadded⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨half, hhalf, hhalfBound⟩
  have hhalfValue : half.val = (exponent.val + 1) / 2 := by
    simpa [Nat.shiftRight_eq_div_pow, hadded, hwiden] using hhalf
  have hround := (LargeSqrt.rounded_half exponent.val hexponent).1
  have hcast : (UScalar.cast .U32 half).val = half.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    rw [hhalfValue]
    norm_num at hround ⊢
    omega
  simp only [WP.spec_ok, hcast, hhalfValue]
  exact ⟨trivial, hround⟩

/-- Appending a recovered byte uses a disjoint bit range and loses no bits. -/
@[step]
theorem large_byte_append_spec (low digit : U32) (count : I32)
    (hcount : count.val = 8 ∨ count.val = 16 ∨ count.val = 24)
    (hlow : low.val < 2 ^ count.val.toNat) (hdigit : digit.val < 256) :
    (do let aligned ← digit <<< count; lift (low ||| aligned))
      ⦃ out => out.val = low.val + 2 ^ count.val.toNat * digit.val ∧
        out.val < 2 ^ (count.val.toNat + 8) ⦄ := by
  have hcountBound : 0 ≤ count.val ∧ count.val < 32 := by omega
  have hpower : 256 * 2 ^ count.val.toNat ≤ 2 ^ 32 := by
    rcases hcount with hcount | hcount | hcount <;> norm_num [hcount, Int.toNat]
  have hdigitShift : digit.val * 2 ^ count.val.toNat < 2 ^ 32 :=
    _root_.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hdigit (by positivity)) hpower
  step +scalarTac -grind with U32.ShiftLeft_IScalar_spec as ⟨aligned, haligned, halignedBound⟩
  have halignedValue : aligned.val = digit.val * 2 ^ count.val.toNat := by
    rw [Nat.shiftLeft_eq] at haligned
    simpa only [U32.size, U32.numBits, UScalarTy.U32_numBits_eq,
      Nat.mod_eq_of_lt hdigitShift] using haligned
  have hjoin : (low ||| aligned).val = low.val + 2 ^ count.val.toNat * digit.val := by
    rw [UScalar.val_or, halignedValue, Nat.or_comm]
    simpa only [mul_comm, add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := count.val.toNat) hlow digit.val).symm
  simp only [lift, WP.spec_ok, hjoin]
  refine ⟨trivial, ?_⟩
  rw [pow_add]
  have hdigitRound : digit.val + 1 ≤ 256 := by omega
  norm_num
  nlinarith only [hlow, hdigitRound]

#print axioms large_low_word
#print axioms large_mask_byte
#print axioms large_mask_parity
#print axioms large_hash_spec
#print axioms large_half_exponent_spec
#print axioms large_byte_append_spec

end UdonVerify.Native
