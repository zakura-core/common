import NativeSqrtOperations
import NativeSqrtMath

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

abbrev Base := SqrtNative.zakura_udon.field.pasta.parameters.PallasBase
abbrev Scalar := SqrtNative.zakura_udon.field.pasta.parameters.PallasScalar
abbrev fpSqrtInst :=
  SqrtNative.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersPrimeModulus
abbrev fqSqrtInst :=
  SqrtNative.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersPrimeModulus

def fpSqrtParameters : PastaParameters (Native.kernelInst (nativeModulus fpSqrtInst)) :=
  Native.transferParameters (Native.kernelInst (nativeModulus fpSqrtInst)) fpParameters
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

def fqSqrtParameters : PastaParameters (Native.kernelInst (nativeModulus fqSqrtInst)) :=
  Native.transferParameters (Native.kernelInst (nativeModulus fqSqrtInst)) fqParameters
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

def fpSqrtConversion : Native.ConversionParameters (nativeModulus fpSqrtInst) fpSqrtParameters where
  radix := Native.fpConversionParameters.radix
  radix2 := Native.fpConversionParameters.radix2
  radix_ok := by with_unfolding_all rfl
  radix2_ok := by with_unfolding_all rfl
  radix_val := Native.fpConversionParameters.radix_val
  radix2_val := Native.fpConversionParameters.radix2_val

def fqSqrtConversion : Native.ConversionParameters (nativeModulus fqSqrtInst) fqSqrtParameters where
  radix := Native.fqConversionParameters.radix
  radix2 := Native.fqConversionParameters.radix2
  radix_ok := by with_unfolding_all rfl
  radix2_ok := by with_unfolding_all rfl
  radix_val := Native.fqConversionParameters.radix_val
  radix2_val := Native.fqConversionParameters.radix2_val

instance fpSqrtPrime : Fact (Nat.Prime (val4 fpSqrtParameters.modulus)) := ⟨Native.fp_prime⟩
instance fqSqrtPrime : Fact (Nat.Prime (val4 fqSqrtParameters.modulus)) := ⟨Native.fq_prime⟩
instance fpPrimeFact : Fact (Nat.Prime Native.fpPrime) := ⟨Native.fp_prime⟩
instance fqPrimeFact : Fact (Nat.Prime Native.fqPrime) := ⟨Native.fq_prime⟩

def fpOperations : Sqrt.Operations (K := ZMod Native.fpPrime) (sqrtInst fpSqrtInst) :=
  nativeOperations fpSqrtInst fpSqrtParameters fpSqrtConversion
    Native.fpRadixInverse Native.fp_radix_inverse

def fqOperations : Sqrt.Operations (K := ZMod Native.fqPrime) (sqrtInst fqSqrtInst) :=
  nativeOperations fqSqrtInst fqSqrtParameters fqSqrtConversion
    Native.fqRadixInverse Native.fq_radix_inverse

#print axioms fpOperations
#print axioms fqOperations

end UdonVerify.SqrtNativeBridge
