import CommonPublicInversionPacking
import CommonInversionInvariant
import CommonNormalizeCarry

open Aeneas Std Result UdonVerify.CommonSigned62
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true

abbrev fqPublicDict : Modulus Native.Scalar := publicDict Native.fqNativeInst
abbrev fqInvDict := CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket fqPublicDict

def fqModulus62 : Signed62 := make62 884652903791329281#i64 655946578822079350#i64 2#i64 0#i64 64#i64
def fqRadix2_62 : Signed62 := make62 4365809925394268175#i64 2228451641930570639#i64 4243007676294846726#i64 1968191643554589279#i64 9#i64

def fqInvHelpers : InvHelperParameters (inversionHelperDict (coreDict fqInvDict)) where
  modulus := fqModulus62
  mu := 3727033114636058625#u64
  modulus_eq := by with_unfolding_all rfl
  mu_eq := by
    change CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket.MU fqPublicDict = ok 3727033114636058625#u64
    rw [public_mu_eq fqPublicDict Native.fqNativeParameters.inv Native.fqNativeParameters.inv_ok]
    congr 1
    decide +kernel
  normalized := by
    intro k
    fin_cases k <;> norm_num [fqModulus62, make62, signedRadix]
  positive := by norm_num [fqModulus62, make62, signed62Value, signedRadix]
  bound := by norm_num [fqModulus62, make62, signed62Value, signedRadix]
  inverse := by norm_num [fqModulus62, make62, signedRadix, Int.ModEq]
  sparse := by norm_num [fqModulus62, make62]

def fqInversionParameters : InversionParameters (coreDict fqInvDict) where
  helpers := fqInvHelpers
  r2 := fqRadix2_62
  r2_eq := by
    change CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket.R2_62 fqPublicDict = ok fqRadix2_62
    apply public_r2_eq fqPublicDict Native.fqConversionParameters.radix2 fqRadix2_62
      Native.fqConversionParameters.radix2_ok
    intro k
    fin_cases k <;> norm_num [packed62Digit, fqRadix2_62, make62, Native.fqConversionParameters,
      NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.R2]
  r2_normalized := by
    intro k
    fin_cases k <;> norm_num [fqRadix2_62, make62, signedRadix]
  r2_range := by norm_num [fqRadix2_62, fqInvHelpers, fqModulus62, make62, signed62Value, signedRadix]
  r2_congruence := by norm_num [fqRadix2_62, fqInvHelpers, fqModulus62, make62, signed62Value, signedRadix, Int.ModEq]
  odd := by norm_num [fqInvHelpers, fqModulus62, make62, signed62Value, signedRadix]
  large := by norm_num [fqInvHelpers, fqModulus62, make62, signed62Value, signedRadix]

theorem fq_inversion_modulus_value : signed62Value fqInversionParameters.helpers.modulus = (Native.fqPrime : Int) := by
  norm_num [fqInversionParameters, fqInvHelpers, fqModulus62, make62, signed62Value, signedRadix,
    Native.fqPrime, fqParameters, val4, B,
    udon_kernel_slice.field.pasta.PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]

#print axioms fqInvHelpers
#print axioms fqInversionParameters
#print axioms fq_inversion_modulus_value
end UdonVerify.PublicInversion
