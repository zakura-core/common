import NativeSqrtAlternate

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

@[step]
theorem fp_sqrt_spec (value : Element Base Reduced) (hvalue : val4 value.limbs < Native.fpPrime) :
    SqrtNative.fp_sqrt value ⦃ out => sqrtResult Native.fpPrime Native.fpRadixInverse
      (fieldValue Native.fpPrime Native.fpRadixInverse value) out ⦄ := by
  unfold SqrtNative.fp_sqrt
  exact sqrt_public_spec fpSqrtInst fpSqrtParameters Native.fpRadixInverse fpConfiguration value hvalue

@[step]
theorem fq_sqrt_spec (value : Element Scalar Reduced) (hvalue : val4 value.limbs < Native.fqPrime) :
    SqrtNative.fq_sqrt value ⦃ out => sqrtResult Native.fqPrime Native.fqRadixInverse
      (fieldValue Native.fqPrime Native.fqRadixInverse value) out ⦄ := by
  unfold SqrtNative.fq_sqrt
  exact sqrt_public_spec fqSqrtInst fqSqrtParameters Native.fqRadixInverse fqConfiguration value hvalue

@[step]
theorem fp_sqrt_alt_spec (value : Element Base Reduced) (hvalue : val4 value.limbs < Native.fpPrime) :
    SqrtNative.fp_sqrt_alt value ⦃ out => sqrtAltResult Native.fpPrime Native.fpRadixInverse
      (fieldValue Native.fpPrime Native.fpRadixInverse value)
      (Native.rootValue Native.fpPrime Native.fpRadixInverse Native.fpRoots 32 : ZMod Native.fpPrime) out ⦄ := by
  unfold SqrtNative.fp_sqrt_alt
  exact sqrt_alt_public_spec fpSqrtInst fpSqrtParameters Native.fpRadixInverse fpConfiguration value hvalue

@[step]
theorem fq_sqrt_alt_spec (value : Element Scalar Reduced) (hvalue : val4 value.limbs < Native.fqPrime) :
    SqrtNative.fq_sqrt_alt value ⦃ out => sqrtAltResult Native.fqPrime Native.fqRadixInverse
      (fieldValue Native.fqPrime Native.fqRadixInverse value)
      (Native.rootValue Native.fqPrime Native.fqRadixInverse Native.fqRoots 32 : ZMod Native.fqPrime) out ⦄ := by
  unfold SqrtNative.fq_sqrt_alt
  exact sqrt_alt_public_spec fqSqrtInst fqSqrtParameters Native.fqRadixInverse fqConfiguration value hvalue

@[step]
theorem fp_sqrt_ratio_spec (num den : Element Base Reduced)
    (hnum : val4 num.limbs < Native.fpPrime) (hden : val4 den.limbs < Native.fpPrime) :
    SqrtNative.fp_sqrt_ratio num den ⦃ out => sqrtRatioResult Native.fpPrime Native.fpRadixInverse
      (fieldValue Native.fpPrime Native.fpRadixInverse num) (fieldValue Native.fpPrime Native.fpRadixInverse den)
      (Native.rootValue Native.fpPrime Native.fpRadixInverse Native.fpRoots 32 : ZMod Native.fpPrime) out ⦄ := by
  unfold SqrtNative.fp_sqrt_ratio
  exact sqrt_ratio_public_spec fpSqrtInst fpSqrtParameters Native.fpRadixInverse fpConfiguration num den hnum hden

@[step]
theorem fq_sqrt_ratio_spec (num den : Element Scalar Reduced)
    (hnum : val4 num.limbs < Native.fqPrime) (hden : val4 den.limbs < Native.fqPrime) :
    SqrtNative.fq_sqrt_ratio num den ⦃ out => sqrtRatioResult Native.fqPrime Native.fqRadixInverse
      (fieldValue Native.fqPrime Native.fqRadixInverse num) (fieldValue Native.fqPrime Native.fqRadixInverse den)
      (Native.rootValue Native.fqPrime Native.fqRadixInverse Native.fqRoots 32 : ZMod Native.fqPrime) out ⦄ := by
  unfold SqrtNative.fq_sqrt_ratio
  exact sqrt_ratio_public_spec fqSqrtInst fqSqrtParameters Native.fqRadixInverse fqConfiguration num den hnum hden

#print axioms fp_sqrt_spec
#print axioms fq_sqrt_spec
#print axioms fp_sqrt_alt_spec
#print axioms fq_sqrt_alt_spec
#print axioms fp_sqrt_ratio_spec
#print axioms fq_sqrt_ratio_spec

end UdonVerify.SqrtNativeBridge
