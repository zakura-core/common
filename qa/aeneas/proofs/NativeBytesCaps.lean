import NativeBytesReduced

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024


@[step]
theorem fp_from_bytes_mod_spec (bytes : Aeneas.Std.Slice U8) :
    NativeField.fp_from_bytes_reduced bytes
      ⦃ out => val4 out.limbs < 2 * fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs = byteValue bytes.val % fpPrime ⦄ := by
  unfold NativeField.fp_from_bytes_reduced
  simpa only [fp_native_prime_eq] using from_bytes_reduced_spec fpNativeInst fpNativeParameters
    fpWideFieldParameters looseInst (2 * fpPrime) fpRadixInverse fp_radix_inverse bytes
    (loose_constructor_value_spec fpNativeInst fpNativeParameters)

#print axioms fp_from_bytes_mod_spec


@[step]
theorem fp_from_bytes_mod_reduced_spec (bytes : Aeneas.Std.Slice U8) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes_reduced fpNativeInst reducedInst bytes
      ⦃ out => val4 out.limbs < fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs = byteValue bytes.val % fpPrime ⦄ := by
  simpa only [fp_native_prime_eq] using from_bytes_reduced_spec fpNativeInst fpNativeParameters
    fpWideFieldParameters reducedInst (fpPrime) fpRadixInverse fp_radix_inverse bytes
    (reduced_constructor_value_spec fpNativeInst fpNativeParameters)

#print axioms fp_from_bytes_mod_reduced_spec


@[step]
theorem fq_from_bytes_mod_spec (bytes : Aeneas.Std.Slice U8) :
    NativeField.fq_from_bytes_reduced bytes
      ⦃ out => val4 out.limbs < 2 * fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs = byteValue bytes.val % fqPrime ⦄ := by
  unfold NativeField.fq_from_bytes_reduced
  simpa only [fq_native_prime_eq] using from_bytes_reduced_spec fqNativeInst fqNativeParameters
    fqWideFieldParameters looseInst (2 * fqPrime) fqRadixInverse fq_radix_inverse bytes
    (loose_constructor_value_spec fqNativeInst fqNativeParameters)

#print axioms fq_from_bytes_mod_spec


@[step]
theorem fq_from_bytes_mod_reduced_spec (bytes : Aeneas.Std.Slice U8) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes_reduced fqNativeInst reducedInst bytes
      ⦃ out => val4 out.limbs < fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs = byteValue bytes.val % fqPrime ⦄ := by
  simpa only [fq_native_prime_eq] using from_bytes_reduced_spec fqNativeInst fqNativeParameters
    fqWideFieldParameters reducedInst (fqPrime) fqRadixInverse fq_radix_inverse bytes
    (reduced_constructor_value_spec fqNativeInst fqNativeParameters)

#print axioms fq_from_bytes_mod_reduced_spec

end UdonVerify.Native
