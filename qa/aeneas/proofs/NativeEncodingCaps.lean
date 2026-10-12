import NativeByteDecode

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem fp_from_canonical_spec (value : CanonicalUint) :
    NativeField.fp_from_canonical value
      ⦃ out => match out with
        | none => fpPrime ≤ val4 value.limbs
        | some result => val4 value.limbs < fpPrime ∧
            val4 result.limbs < 2 * fpPrime ∧
            decode fpPrime fpRadixInverse result.limbs = val4 value.limbs ⦄ := by
  unfold NativeField.fp_from_canonical
  apply WP.spec_mono (from_canonical_uint_spec fpNativeInst fpNativeParameters looseInst (2 * fpPrime) fpRadixInverse value
    (fun limbs hlimbs => from_canonical_loose_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse limbs hlimbs))
  intro out hout
  cases out <;> simpa only [fp_native_prime_eq] using hout

@[step]
theorem fp_to_canonical_spec (value : Element Base Loose)
    (ha : val4 value.limbs < 2 * fpPrime) :
    NativeField.fp_to_canonical value
      ⦃ out => val4 out.limbs < fpPrime ∧
        val4 out.limbs = decode fpPrime fpRadixInverse value.limbs ⦄ := by
  unfold NativeField.fp_to_canonical
  simpa only [fp_native_prime_eq] using to_canonical_uint_spec fpNativeInst fpNativeParameters value fpRadixInverse fp_radix_inverse ha

@[step]
theorem fp_from_uint_reduced_spec (value : CanonicalUint) :
    NativeField.fp_from_uint_reduced value
      ⦃ out => val4 out.limbs < 2 * fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs = val4 value.limbs % fpPrime ⦄ := by
  unfold NativeField.fp_from_uint_reduced
  apply from_uint_reduced_spec fpNativeInst fpNativeParameters fpConversionParameters looseInst
    (2 * fpPrime) fpRadixInverse fp_radix_inverse value
  intro limbs hlimbs
  step -grind with (from_loose_loose_spec fpNativeInst fpNativeParameters limbs hlimbs) as ⟨out, hout⟩
  refine ⟨by simpa only [hout, fp_native_prime_eq] using hlimbs, ?_⟩
  rw [hout]

@[step]
theorem fp_from_canonical_reduced_spec (value : CanonicalUint) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_uint fpNativeInst reducedInst value
      ⦃ out => match out with
        | none => fpPrime ≤ val4 value.limbs
        | some result => val4 value.limbs < fpPrime ∧
            val4 result.limbs < fpPrime ∧
            decode fpPrime fpRadixInverse result.limbs = val4 value.limbs ⦄ := by
  apply WP.spec_mono (from_canonical_uint_spec fpNativeInst fpNativeParameters reducedInst (fpPrime) fpRadixInverse value
    (fun limbs hlimbs => from_canonical_reduced_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse limbs hlimbs))
  intro out hout
  cases out <;> simpa only [fp_native_prime_eq] using hout

@[step]
theorem fp_to_canonical_reduced_spec (value : Element Base Reduced)
    (ha : val4 value.limbs < fpPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_canonical_uint fpNativeInst value
      ⦃ out => val4 out.limbs < fpPrime ∧
        val4 out.limbs = decode fpPrime fpRadixInverse value.limbs ⦄ := by
  simpa only [fp_native_prime_eq] using to_canonical_uint_spec fpNativeInst fpNativeParameters value fpRadixInverse fp_radix_inverse (by rw [fp_native_prime_eq]; omega)

@[step]
theorem fp_from_uint_reduced_reduced_spec (value : CanonicalUint) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_uint_reduced fpNativeInst reducedInst value
      ⦃ out => val4 out.limbs < fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs = val4 value.limbs % fpPrime ⦄ := by
  apply from_uint_reduced_spec fpNativeInst fpNativeParameters fpConversionParameters reducedInst
    (fpPrime) fpRadixInverse fp_radix_inverse value
  intro limbs hlimbs
  step -grind with (from_loose_reduced_spec fpNativeInst fpNativeParameters limbs hlimbs)
    as ⟨out, hbound, hout⟩
  refine ⟨hbound, ?_⟩
  simp only [Nat.ModEq, hout, Nat.mod_mod]

@[step]
theorem fq_from_canonical_spec (value : CanonicalUint) :
    NativeField.fq_from_canonical value
      ⦃ out => match out with
        | none => fqPrime ≤ val4 value.limbs
        | some result => val4 value.limbs < fqPrime ∧
            val4 result.limbs < 2 * fqPrime ∧
            decode fqPrime fqRadixInverse result.limbs = val4 value.limbs ⦄ := by
  unfold NativeField.fq_from_canonical
  apply WP.spec_mono (from_canonical_uint_spec fqNativeInst fqNativeParameters looseInst (2 * fqPrime) fqRadixInverse value
    (fun limbs hlimbs => from_canonical_loose_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse limbs hlimbs))
  intro out hout
  cases out <;> simpa only [fq_native_prime_eq] using hout

@[step]
theorem fq_to_canonical_spec (value : Element Scalar Loose)
    (ha : val4 value.limbs < 2 * fqPrime) :
    NativeField.fq_to_canonical value
      ⦃ out => val4 out.limbs < fqPrime ∧
        val4 out.limbs = decode fqPrime fqRadixInverse value.limbs ⦄ := by
  unfold NativeField.fq_to_canonical
  simpa only [fq_native_prime_eq] using to_canonical_uint_spec fqNativeInst fqNativeParameters value fqRadixInverse fq_radix_inverse ha

@[step]
theorem fq_from_uint_reduced_spec (value : CanonicalUint) :
    NativeField.fq_from_uint_reduced value
      ⦃ out => val4 out.limbs < 2 * fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs = val4 value.limbs % fqPrime ⦄ := by
  unfold NativeField.fq_from_uint_reduced
  apply from_uint_reduced_spec fqNativeInst fqNativeParameters fqConversionParameters looseInst
    (2 * fqPrime) fqRadixInverse fq_radix_inverse value
  intro limbs hlimbs
  step -grind with (from_loose_loose_spec fqNativeInst fqNativeParameters limbs hlimbs) as ⟨out, hout⟩
  refine ⟨by simpa only [hout, fq_native_prime_eq] using hlimbs, ?_⟩
  rw [hout]

@[step]
theorem fq_from_canonical_reduced_spec (value : CanonicalUint) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_uint fqNativeInst reducedInst value
      ⦃ out => match out with
        | none => fqPrime ≤ val4 value.limbs
        | some result => val4 value.limbs < fqPrime ∧
            val4 result.limbs < fqPrime ∧
            decode fqPrime fqRadixInverse result.limbs = val4 value.limbs ⦄ := by
  apply WP.spec_mono (from_canonical_uint_spec fqNativeInst fqNativeParameters reducedInst (fqPrime) fqRadixInverse value
    (fun limbs hlimbs => from_canonical_reduced_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse limbs hlimbs))
  intro out hout
  cases out <;> simpa only [fq_native_prime_eq] using hout

@[step]
theorem fq_to_canonical_reduced_spec (value : Element Scalar Reduced)
    (ha : val4 value.limbs < fqPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_canonical_uint fqNativeInst value
      ⦃ out => val4 out.limbs < fqPrime ∧
        val4 out.limbs = decode fqPrime fqRadixInverse value.limbs ⦄ := by
  simpa only [fq_native_prime_eq] using to_canonical_uint_spec fqNativeInst fqNativeParameters value fqRadixInverse fq_radix_inverse (by rw [fq_native_prime_eq]; omega)

@[step]
theorem fq_from_uint_reduced_reduced_spec (value : CanonicalUint) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_uint_reduced fqNativeInst reducedInst value
      ⦃ out => val4 out.limbs < fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs = val4 value.limbs % fqPrime ⦄ := by
  apply from_uint_reduced_spec fqNativeInst fqNativeParameters fqConversionParameters reducedInst
    (fqPrime) fqRadixInverse fq_radix_inverse value
  intro limbs hlimbs
  step -grind with (from_loose_reduced_spec fqNativeInst fqNativeParameters limbs hlimbs)
    as ⟨out, hbound, hout⟩
  refine ⟨hbound, ?_⟩
  simp only [Nat.ModEq, hout, Nat.mod_mod]

#print axioms fp_from_canonical_spec
#print axioms fq_from_uint_reduced_spec

end UdonVerify.Native
