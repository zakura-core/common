import NativeBasics

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

/-- Additional native constants needed to connect constructors to ordinary integers. -/
structure ConversionParameters {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) where
  radix : A4
  radix2 : A4
  radix_ok : inst.sealedParametersInst.R = ok radix
  radix2_ok : inst.sealedParametersInst.R2 = ok radix2
  radix_val : val4 radix = R%val4 params.modulus
  radix2_val : val4 radix2 = R^2%val4 params.modulus

def fpConversionParameters : ConversionParameters fpNativeInst fpNativeParameters where
  radix := NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.R
  radix2 := NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.R2
  radix_ok := by with_unfolding_all rfl
  radix2_ok := by with_unfolding_all rfl
  radix_val := by
    norm_num [val4,R,B,fpNativeParameters,transferParameters,fpParameters,
      NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.R,
      udon_kernel_slice.field.pasta.PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]
  radix2_val := by
    norm_num [val4,R,B,fpNativeParameters,transferParameters,fpParameters,
      NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.R2,
      udon_kernel_slice.field.pasta.PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]

def fqConversionParameters : ConversionParameters fqNativeInst fqNativeParameters where
  radix := NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.R
  radix2 := NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.R2
  radix_ok := by with_unfolding_all rfl
  radix2_ok := by with_unfolding_all rfl
  radix_val := by
    norm_num [val4,R,B,fqNativeParameters,transferParameters,fqParameters,
      NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.R,
      udon_kernel_slice.field.pasta.PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]
  radix2_val := by
    norm_num [val4,R,B,fqNativeParameters,transferParameters,fqParameters,
      NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.R2,
      udon_kernel_slice.field.pasta.PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]

theorem decoded_conversion (p inverse a r2 u m : Nat)
    (hinverse : Nat.ModEq p (R*inverse) 1)
    (hr2 : Nat.ModEq p r2 (R^2)) (hcert : R*u=a*r2+m*p) :
    (u*inverse)%p = a%p := by
  have hcertmod := certificate_congruence p (a*r2) m u hcert
  have hscaled : Nat.ModEq p ((R*inverse)*(u*inverse)) (a*r2*inverse^2) := by
    convert hcertmod.mul_right (inverse^2) using 1 <;> ring
  have hcancel : Nat.ModEq p ((R*inverse)*(u*inverse)) (u*inverse) := by
    simpa only [one_mul] using hinverse.mul_right (u*inverse)
  have hr2scaled : Nat.ModEq p (a*r2*inverse^2) (a*(R*inverse)^2) := by
    convert (hr2.mul_left a).mul_right (inverse^2) using 1 <;> ring
  have hright : Nat.ModEq p (a*(R*inverse)^2) a := by
    simpa only [one_pow,mul_one] using (hinverse.pow 2).mul_left a
  exact hcancel.symm.trans (hscaled.trans (hr2scaled.trans hright))

#print axioms fpConversionParameters
#print axioms fqConversionParameters

end UdonVerify.Native
