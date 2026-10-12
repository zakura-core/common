import NativeRawProducts
import NativeByteDecode

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev Bytes64 := Array U8 64#usize

theorem decoded_raw_conversion (p inverse input product out m : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hproduct : Nat.ModEq p product (input * R ^ 2))
    (hcert : R * out = product + m * p) :
    (out * inverse) % p = input % p := by
  have hc := (certificate_congruence p product m out hcert).trans hproduct
  have hscaled : Nat.ModEq p ((R * inverse) * (out * inverse))
      (input * (R * inverse) ^ 2) := by
    convert hc.mul_right (inverse ^ 2) using 1 <;> ring
  have hleft : Nat.ModEq p ((R * inverse) * (out * inverse)) (out * inverse) := by
    simpa only [one_mul] using hinverse.mul_right (out * inverse)
  have hright : Nat.ModEq p (input * (R * inverse) ^ 2) input := by
    simpa only [one_pow, mul_one] using (hinverse.pow 2).mul_left input
  exact hleft.symm.trans (hscaled.trans hright)

theorem byteValue_halves (bytes : Bytes64) :
    byteValue bytes.val = byteValue (bytes.val.slice 0 32) +
      R * byteValue (bytes.val.slice 32 64) := by
  have hsplit : bytes.val = bytes.val.slice 0 32 ++ bytes.val.slice 32 64 := by
    calc
      bytes.val = bytes.val.take 64 := by simp
      _ = bytes.val.take 32 ++ (bytes.val.drop 32).take 32 :=
        List.take_add (i := 32) (j := 32)
      _ = _ := by simp [List.slice]
  have hlen : (bytes.val.slice 0 32).length = 32 := by simp [List.slice_length]
  conv_lhs => rw [hsplit]
  rw [byteValue_append, hlen]
  norm_num [R, B]

/-- Every 64-byte input is reduced modulo the modulus, in either reduction state. -/
@[step]
theorem from_wide_bytes_reduced_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (bound inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (bytes : Bytes64)
    (hconstructor : ∀ limbs : A4, val4 limbs < 2 * val4 params.modulus →
      NativeField.zakura_udon.field.pasta.PastaField.from_loose inst state limbs
        ⦃ out => val4 out.limbs < bound ∧
          Nat.ModEq (val4 params.modulus) (val4 out.limbs) (val4 limbs) ⦄) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_wide_bytes_reduced
      inst state bytes ⦃ out => val4 out.limbs < bound ∧
        decode (val4 params.modulus) inverse out.limbs =
          byteValue bytes.val % val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.from_wide_bytes_reduced
  simp only [NativeField.zakura_udon.field.pasta.ENCODED_SIZE]
  have hlen64 : (Array.to_slice bytes).length = 64 := by
    simp [Array.to_slice, Slice.length]
  step +scalarTac -grind as ⟨lowSlice, hlowSlice, hlowLen⟩
  step -grind as ⟨lowResult, hlowResult⟩
  cases lowResult with
  | Err error => cases error; simp only at hlowResult; omega
  | Ok lowBytes =>
    simp only at hlowResult
    simp only [core.result.Result.unwrap, bind_ok]
    step -grind with (uint_from_bytes_spec lowBytes) as ⟨low, hlow⟩
    step +scalarTac -grind as ⟨highSlice, hhighSlice, hhighLen⟩
    step -grind as ⟨highResult, hhighResult⟩
    cases highResult with
    | Err error => cases error; simp only at hhighResult; omega
    | Ok highBytes =>
      simp only at hhighResult
      simp only [core.result.Result.unwrap, bind_ok,
        NativeField.zakura_udon.field.pasta.uint.CanonicalUint.impl.limbs]
      step -grind with (uint_from_bytes_spec highBytes) as ⟨high, hhigh⟩
      rw [constants.conversion.radix2_ok, constants.radix3_ok]
      simp only [bind_ok, NativeField.zakura_udon.field.pasta.uint.CanonicalUint.impl.limbs]
      have hboundProducts := two_raw_products_bound inst params constants
        (val4 low.limbs) (val4 high.limbs) (val4_lt _) (val4_lt _)
      step -grind with (raw_product_sum_spec inst params low.limbs constants.conversion.radix2
        high.limbs constants.radix3 hboundProducts) as ⟨limbs, hlimbs, m, hm, hcert⟩
      step -grind with (hconstructor limbs hlimbs) as ⟨out, hout, hcongruence⟩
      refine ⟨hout, ?_⟩
      have hr2 : Nat.ModEq (val4 params.modulus) (val4 constants.conversion.radix2) (R ^ 2) := by
        simp only [Nat.ModEq, constants.conversion.radix2_val, Nat.mod_mod]
      have hr3 : Nat.ModEq (val4 params.modulus) (val4 constants.radix3) (R ^ 3) := by
        simp only [Nat.ModEq, constants.radix3_val, Nat.mod_mod]
      have hproduct : Nat.ModEq (val4 params.modulus)
          (val4 low.limbs * val4 constants.conversion.radix2 + val4 high.limbs * val4 constants.radix3)
          ((val4 low.limbs + R * val4 high.limbs) * R ^ 2) := by
        convert (hr2.mul_left (val4 low.limbs)).add (hr3.mul_left (val4 high.limbs)) using 1 <;> ring
      have hdecode := decoded_raw_conversion (val4 params.modulus) inverse
        (val4 low.limbs + R * val4 high.limbs) _ (val4 limbs) m hinverse hproduct hcert
      have hlowVal : val4 low.limbs = byteValue (bytes.val.slice 0 32) := by
        rw [hlow, hlowResult.1, hlowSlice]
        simp [Array.to_slice, List.slice]
      have hhighVal : val4 high.limbs = byteValue (bytes.val.slice 32 64) := by
        rw [hhigh, hhighResult.1, hhighSlice]
        have htail : (bytes.val.drop 32).take 32 = bytes.val.drop 32 := by
          apply List.take_of_length_le
          simp
        simp [Array.to_slice, List.slice, htail]
      unfold decode
      exact (hcongruence.mul_right inverse).trans
        (by simpa only [Nat.ModEq, hlowVal, hhighVal, byteValue_halves] using hdecode)

#print axioms decoded_raw_conversion
#print axioms byteValue_halves
#print axioms from_wide_bytes_reduced_spec

end UdonVerify.Native
