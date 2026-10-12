import CommonPublicInversionPacking
import CommonInversionInvariant
import CommonNormalizeCarry

open Aeneas Std Result UdonVerify.CommonSigned62
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true

abbrev fpPublicDict : Modulus Native.Base := publicDict Native.fpNativeInst
abbrev fpInvDict := CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket fpPublicDict

def fpModulus62 : Signed62 := make62 1814160019365560321#i64 655946578803287150#i64 2#i64 0#i64 64#i64
def fpRadix2_62 : Signed62 := make62 898728379203715087#i64 2255237944337466270#i64 4141791841069945229#i64 1968191642266354973#i64 9#i64

def fpInvHelpers : InvHelperParameters (inversionHelperDict (coreDict fpInvDict)) where
  modulus := fpModulus62
  mu := 2797525999061827585#u64
  modulus_eq := by with_unfolding_all rfl
  mu_eq := by
    change CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket.MU fpPublicDict = ok 2797525999061827585#u64
    rw [public_mu_eq fpPublicDict Native.fpNativeParameters.inv Native.fpNativeParameters.inv_ok]
    congr 1
    decide +kernel
  normalized := by
    intro k
    fin_cases k <;> norm_num [fpModulus62, make62, signedRadix]
  positive := by norm_num [fpModulus62, make62, signed62Value, signedRadix]
  bound := by norm_num [fpModulus62, make62, signed62Value, signedRadix]
  inverse := by norm_num [fpModulus62, make62, signedRadix, Int.ModEq]
  sparse := by norm_num [fpModulus62, make62]

def fpInversionParameters : InversionParameters (coreDict fpInvDict) where
  helpers := fpInvHelpers
  r2 := fpRadix2_62
  r2_eq := by
    change CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket.R2_62 fpPublicDict = ok fpRadix2_62
    apply public_r2_eq fpPublicDict Native.fpConversionParameters.radix2 fpRadix2_62
      Native.fpConversionParameters.radix2_ok
    intro k
    fin_cases k <;> norm_num [packed62Digit, fpRadix2_62, make62, Native.fpConversionParameters,
      NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.R2]
  r2_normalized := by
    intro k
    fin_cases k <;> norm_num [fpRadix2_62, make62, signedRadix]
  r2_range := by norm_num [fpRadix2_62, fpInvHelpers, fpModulus62, make62, signed62Value, signedRadix]
  r2_congruence := by norm_num [fpRadix2_62, fpInvHelpers, fpModulus62, make62, signed62Value, signedRadix, Int.ModEq]
  odd := by norm_num [fpInvHelpers, fpModulus62, make62, signed62Value, signedRadix]
  large := by norm_num [fpInvHelpers, fpModulus62, make62, signed62Value, signedRadix]

theorem fp_inversion_modulus_value : signed62Value fpInversionParameters.helpers.modulus = (Native.fpPrime : Int) := by
  norm_num [fpInversionParameters, fpInvHelpers, fpModulus62, make62, signed62Value, signedRadix,
    Native.fpPrime, fpParameters, val4, B,
    udon_kernel_slice.field.pasta.PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]

#print axioms fpInvHelpers
#print axioms fpInversionParameters
#print axioms fp_inversion_modulus_value
end UdonVerify.PublicInversion
