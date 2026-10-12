import CommonFPInversionParameters
import CommonFQInversionParameters
import CommonPublicInversionAPI
import CommonPublicInversionStates
import CommonInversionComplete
import PastaPrimality

open Aeneas Std Result UdonVerify.CommonSigned62
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024


@[step]
theorem fp_invert_loose_spec (value : Element Native.Base Native.Loose)
    (hbound : val4 value.limbs < 2 * Native.fpPrime) :
    CommonPublicInversion.field.pasta.inversion.PastaField.invert fpPublicDict looseInputInst value ⦃ out =>
      FieldInversionResult Native.fpPrime Native.fpRadixInverse value out ⦄ := by
  apply public_invert_conditional_spec fpPublicDict Native.fpNativeParameters fpInversionParameters
    fp_inversion_modulus_value Native.fp_prime Native.fpRadixInverse Native.fp_radix_inverse
    looseInputInst false (by with_unfolding_all rfl) value hbound
  intro n hn
  apply inversion_converges fpInversionParameters (n : Int)
  constructor
  · omega
  · rw [fp_inversion_modulus_value]
    exact_mod_cast hn

#print axioms fp_invert_loose_spec

@[step]
theorem fp_invert_reduced_spec (value : Element Native.Base Native.Reduced)
    (hbound : val4 value.limbs < Native.fpPrime) :
    CommonPublicInversion.field.pasta.inversion.PastaField.invert fpPublicDict reducedInputInst value ⦃ out =>
      FieldInversionResult Native.fpPrime Native.fpRadixInverse value out ⦄ := by
  apply public_invert_conditional_spec fpPublicDict Native.fpNativeParameters fpInversionParameters
    fp_inversion_modulus_value Native.fp_prime Native.fpRadixInverse Native.fp_radix_inverse
    reducedInputInst true (by with_unfolding_all rfl) value hbound
  intro n hn
  apply inversion_converges fpInversionParameters (n : Int)
  constructor
  · omega
  · rw [fp_inversion_modulus_value]
    exact_mod_cast hn

#print axioms fp_invert_reduced_spec

@[step]
theorem fq_invert_loose_spec (value : Element Native.Scalar Native.Loose)
    (hbound : val4 value.limbs < 2 * Native.fqPrime) :
    CommonPublicInversion.field.pasta.inversion.PastaField.invert fqPublicDict looseInputInst value ⦃ out =>
      FieldInversionResult Native.fqPrime Native.fqRadixInverse value out ⦄ := by
  apply public_invert_conditional_spec fqPublicDict Native.fqNativeParameters fqInversionParameters
    fq_inversion_modulus_value Native.fq_prime Native.fqRadixInverse Native.fq_radix_inverse
    looseInputInst false (by with_unfolding_all rfl) value hbound
  intro n hn
  apply inversion_converges fqInversionParameters (n : Int)
  constructor
  · omega
  · rw [fq_inversion_modulus_value]
    exact_mod_cast hn

#print axioms fq_invert_loose_spec

@[step]
theorem fq_invert_reduced_spec (value : Element Native.Scalar Native.Reduced)
    (hbound : val4 value.limbs < Native.fqPrime) :
    CommonPublicInversion.field.pasta.inversion.PastaField.invert fqPublicDict reducedInputInst value ⦃ out =>
      FieldInversionResult Native.fqPrime Native.fqRadixInverse value out ⦄ := by
  apply public_invert_conditional_spec fqPublicDict Native.fqNativeParameters fqInversionParameters
    fq_inversion_modulus_value Native.fq_prime Native.fqRadixInverse Native.fq_radix_inverse
    reducedInputInst true (by with_unfolding_all rfl) value hbound
  intro n hn
  apply inversion_converges fqInversionParameters (n : Int)
  constructor
  · omega
  · rw [fq_inversion_modulus_value]
    exact_mod_cast hn

#print axioms fq_invert_reduced_spec

end UdonVerify.PublicInversion
