import NativeConstants

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

/-- Compiled constants and exact bounds for wider decoding and deferred sums. -/
structure WideFieldParameters {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) where
  conversion : ConversionParameters inst params
  radix3 : A4
  high448 : A4
  radix3_ok : inst.sealedParametersInst.R3 = ok radix3
  high448_ok : inst.sealedParametersInst.B448 = ok high448
  radix3_val : val4 radix3 = R ^ 3 % val4 params.modulus
  high448_val : val4 high448 = B ^ 7 % val4 params.modulus
  wide_bound : val4 conversion.radix2 + val4 radix3 < val4 params.modulus
  horner_bound : (2 * val4 params.modulus + R) * val4 conversion.radix2 <
    val4 params.modulus * R

def fpWideFieldParameters : WideFieldParameters fpNativeInst fpNativeParameters where
  conversion := fpConversionParameters
  radix3 := NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.R3
  high448 := NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.B448
  radix3_ok := by with_unfolding_all rfl
  high448_ok := by with_unfolding_all rfl
  radix3_val := by with_unfolding_all decide
  high448_val := by with_unfolding_all decide
  wide_bound := by with_unfolding_all decide
  horner_bound := by with_unfolding_all decide

def fqWideFieldParameters : WideFieldParameters fqNativeInst fqNativeParameters where
  conversion := fqConversionParameters
  radix3 := NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.R3
  high448 := NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.B448
  radix3_ok := by with_unfolding_all rfl
  high448_ok := by with_unfolding_all rfl
  radix3_val := by with_unfolding_all decide
  high448_val := by with_unfolding_all decide
  wide_bound := by with_unfolding_all decide
  horner_bound := by with_unfolding_all decide

#print axioms fpWideFieldParameters
#print axioms fqWideFieldParameters

end UdonVerify.Native
