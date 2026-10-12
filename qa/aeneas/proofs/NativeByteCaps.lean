import NativeEncoding

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem fp_from_bytes_spec (bytes : Bytes32) :
    NativeField.fp_from_bytes bytes
      ⦃ out => match out with
        | none => fpPrime ≤ byteValue bytes.val
        | some result => byteValue bytes.val < fpPrime ∧ val4 result.limbs < 2 * fpPrime ∧
            decode fpPrime fpRadixInverse result.limbs = byteValue bytes.val ⦄ := by
  unfold NativeField.fp_from_bytes
  apply WP.spec_mono (from_bytes_spec fpNativeInst fpNativeParameters looseInst (2 * fpPrime)
    fpRadixInverse bytes (fun limbs hlimbs => from_canonical_loose_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse limbs hlimbs))
  intro out hout
  cases out <;> simpa only [fp_native_prime_eq] using hout

@[step]
theorem fp_to_bytes_spec (value : Element Base Loose)
    (ha : val4 value.limbs < 2 * fpPrime) :
    NativeField.fp_to_bytes value
      ⦃ out => byteValue out.val < fpPrime ∧
        byteValue out.val = decode fpPrime fpRadixInverse value.limbs ⦄ := by
  unfold NativeField.fp_to_bytes
  simpa only [fp_native_prime_eq] using to_bytes_spec fpNativeInst fpNativeParameters value fpRadixInverse fp_radix_inverse
    (by rw [fp_native_prime_eq]; try omega)

theorem fp_canonical_bytes_roundtrip (bytes : Bytes32)
    (hbytes : byteValue bytes.val < fpPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fpNativeInst looseInst bytes
      ⦃ out => ∃ value : Element Base Loose, out = some value ∧
        NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fpNativeInst value
          ⦃ encoded => encoded = bytes ⦄ ⦄ := by
  exact canonical_bytes_roundtrip fpNativeInst fpNativeParameters looseInst fpRadixInverse fp_radix_inverse (2 * fpPrime)
    (by rw [fp_native_prime_eq]; try omega) bytes (by simpa only [fp_native_prime_eq] using hbytes) (fun limbs hlimbs => from_canonical_loose_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse limbs hlimbs)

theorem fp_field_bytes_roundtrip (value : Element Base Loose)
    (ha : val4 value.limbs < 2 * fpPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fpNativeInst value
      ⦃ bytes => NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fpNativeInst looseInst bytes
        ⦃ out => ∃ decoded : Element Base Loose, out = some decoded ∧
          val4 decoded.limbs < 2 * fpPrime ∧ decode fpPrime fpRadixInverse decoded.limbs =
            decode fpPrime fpRadixInverse value.limbs ⦄ ⦄ := by
  simpa only [fp_native_prime_eq] using field_bytes_roundtrip fpNativeInst fpNativeParameters looseInst fpRadixInverse fp_radix_inverse
    (2 * fpPrime) value (by rw [fp_native_prime_eq]; try omega) (fun limbs hlimbs => from_canonical_loose_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse limbs hlimbs)

@[step]
theorem fp_from_bytes_reduced_spec (bytes : Bytes32) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fpNativeInst reducedInst bytes
      ⦃ out => match out with
        | none => fpPrime ≤ byteValue bytes.val
        | some result => byteValue bytes.val < fpPrime ∧ val4 result.limbs < fpPrime ∧
            decode fpPrime fpRadixInverse result.limbs = byteValue bytes.val ⦄ := by
  apply WP.spec_mono (from_bytes_spec fpNativeInst fpNativeParameters reducedInst (fpPrime)
    fpRadixInverse bytes (fun limbs hlimbs => from_canonical_reduced_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse limbs hlimbs))
  intro out hout
  cases out <;> simpa only [fp_native_prime_eq] using hout

@[step]
theorem fp_to_bytes_reduced_spec (value : Element Base Reduced)
    (ha : val4 value.limbs < fpPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fpNativeInst value
      ⦃ out => byteValue out.val < fpPrime ∧
        byteValue out.val = decode fpPrime fpRadixInverse value.limbs ⦄ := by
  simpa only [fp_native_prime_eq] using to_bytes_spec fpNativeInst fpNativeParameters value fpRadixInverse fp_radix_inverse
    (by rw [fp_native_prime_eq]; try omega)

theorem fp_canonical_bytes_roundtrip_reduced (bytes : Bytes32)
    (hbytes : byteValue bytes.val < fpPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fpNativeInst reducedInst bytes
      ⦃ out => ∃ value : Element Base Reduced, out = some value ∧
        NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fpNativeInst value
          ⦃ encoded => encoded = bytes ⦄ ⦄ := by
  exact canonical_bytes_roundtrip fpNativeInst fpNativeParameters reducedInst fpRadixInverse fp_radix_inverse (fpPrime)
    (by rw [fp_native_prime_eq]; try omega) bytes (by simpa only [fp_native_prime_eq] using hbytes) (fun limbs hlimbs => from_canonical_reduced_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse limbs hlimbs)

theorem fp_field_bytes_roundtrip_reduced (value : Element Base Reduced)
    (ha : val4 value.limbs < fpPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fpNativeInst value
      ⦃ bytes => NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fpNativeInst reducedInst bytes
        ⦃ out => ∃ decoded : Element Base Reduced, out = some decoded ∧
          val4 decoded.limbs < fpPrime ∧ decode fpPrime fpRadixInverse decoded.limbs =
            decode fpPrime fpRadixInverse value.limbs ⦄ ⦄ := by
  simpa only [fp_native_prime_eq] using field_bytes_roundtrip fpNativeInst fpNativeParameters reducedInst fpRadixInverse fp_radix_inverse
    (fpPrime) value (by rw [fp_native_prime_eq]; try omega) (fun limbs hlimbs => from_canonical_reduced_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse limbs hlimbs)

@[step]
theorem fq_from_bytes_spec (bytes : Bytes32) :
    NativeField.fq_from_bytes bytes
      ⦃ out => match out with
        | none => fqPrime ≤ byteValue bytes.val
        | some result => byteValue bytes.val < fqPrime ∧ val4 result.limbs < 2 * fqPrime ∧
            decode fqPrime fqRadixInverse result.limbs = byteValue bytes.val ⦄ := by
  unfold NativeField.fq_from_bytes
  apply WP.spec_mono (from_bytes_spec fqNativeInst fqNativeParameters looseInst (2 * fqPrime)
    fqRadixInverse bytes (fun limbs hlimbs => from_canonical_loose_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse limbs hlimbs))
  intro out hout
  cases out <;> simpa only [fq_native_prime_eq] using hout

@[step]
theorem fq_to_bytes_spec (value : Element Scalar Loose)
    (ha : val4 value.limbs < 2 * fqPrime) :
    NativeField.fq_to_bytes value
      ⦃ out => byteValue out.val < fqPrime ∧
        byteValue out.val = decode fqPrime fqRadixInverse value.limbs ⦄ := by
  unfold NativeField.fq_to_bytes
  simpa only [fq_native_prime_eq] using to_bytes_spec fqNativeInst fqNativeParameters value fqRadixInverse fq_radix_inverse
    (by rw [fq_native_prime_eq]; try omega)

theorem fq_canonical_bytes_roundtrip (bytes : Bytes32)
    (hbytes : byteValue bytes.val < fqPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fqNativeInst looseInst bytes
      ⦃ out => ∃ value : Element Scalar Loose, out = some value ∧
        NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fqNativeInst value
          ⦃ encoded => encoded = bytes ⦄ ⦄ := by
  exact canonical_bytes_roundtrip fqNativeInst fqNativeParameters looseInst fqRadixInverse fq_radix_inverse (2 * fqPrime)
    (by rw [fq_native_prime_eq]; try omega) bytes (by simpa only [fq_native_prime_eq] using hbytes) (fun limbs hlimbs => from_canonical_loose_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse limbs hlimbs)

theorem fq_field_bytes_roundtrip (value : Element Scalar Loose)
    (ha : val4 value.limbs < 2 * fqPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fqNativeInst value
      ⦃ bytes => NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fqNativeInst looseInst bytes
        ⦃ out => ∃ decoded : Element Scalar Loose, out = some decoded ∧
          val4 decoded.limbs < 2 * fqPrime ∧ decode fqPrime fqRadixInverse decoded.limbs =
            decode fqPrime fqRadixInverse value.limbs ⦄ ⦄ := by
  simpa only [fq_native_prime_eq] using field_bytes_roundtrip fqNativeInst fqNativeParameters looseInst fqRadixInverse fq_radix_inverse
    (2 * fqPrime) value (by rw [fq_native_prime_eq]; try omega) (fun limbs hlimbs => from_canonical_loose_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse limbs hlimbs)

@[step]
theorem fq_from_bytes_reduced_spec (bytes : Bytes32) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fqNativeInst reducedInst bytes
      ⦃ out => match out with
        | none => fqPrime ≤ byteValue bytes.val
        | some result => byteValue bytes.val < fqPrime ∧ val4 result.limbs < fqPrime ∧
            decode fqPrime fqRadixInverse result.limbs = byteValue bytes.val ⦄ := by
  apply WP.spec_mono (from_bytes_spec fqNativeInst fqNativeParameters reducedInst (fqPrime)
    fqRadixInverse bytes (fun limbs hlimbs => from_canonical_reduced_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse limbs hlimbs))
  intro out hout
  cases out <;> simpa only [fq_native_prime_eq] using hout

@[step]
theorem fq_to_bytes_reduced_spec (value : Element Scalar Reduced)
    (ha : val4 value.limbs < fqPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fqNativeInst value
      ⦃ out => byteValue out.val < fqPrime ∧
        byteValue out.val = decode fqPrime fqRadixInverse value.limbs ⦄ := by
  simpa only [fq_native_prime_eq] using to_bytes_spec fqNativeInst fqNativeParameters value fqRadixInverse fq_radix_inverse
    (by rw [fq_native_prime_eq]; try omega)

theorem fq_canonical_bytes_roundtrip_reduced (bytes : Bytes32)
    (hbytes : byteValue bytes.val < fqPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fqNativeInst reducedInst bytes
      ⦃ out => ∃ value : Element Scalar Reduced, out = some value ∧
        NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fqNativeInst value
          ⦃ encoded => encoded = bytes ⦄ ⦄ := by
  exact canonical_bytes_roundtrip fqNativeInst fqNativeParameters reducedInst fqRadixInverse fq_radix_inverse (fqPrime)
    (by rw [fq_native_prime_eq]; try omega) bytes (by simpa only [fq_native_prime_eq] using hbytes) (fun limbs hlimbs => from_canonical_reduced_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse limbs hlimbs)

theorem fq_field_bytes_roundtrip_reduced (value : Element Scalar Reduced)
    (ha : val4 value.limbs < fqPrime) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.to_bytes fqNativeInst value
      ⦃ bytes => NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes fqNativeInst reducedInst bytes
        ⦃ out => ∃ decoded : Element Scalar Reduced, out = some decoded ∧
          val4 decoded.limbs < fqPrime ∧ decode fqPrime fqRadixInverse decoded.limbs =
            decode fqPrime fqRadixInverse value.limbs ⦄ ⦄ := by
  simpa only [fq_native_prime_eq] using field_bytes_roundtrip fqNativeInst fqNativeParameters reducedInst fqRadixInverse fq_radix_inverse
    (fqPrime) value (by rw [fq_native_prime_eq]; try omega) (fun limbs hlimbs => from_canonical_reduced_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse limbs hlimbs)

#print axioms fp_field_bytes_roundtrip
#print axioms fq_canonical_bytes_roundtrip_reduced

end UdonVerify.Native
