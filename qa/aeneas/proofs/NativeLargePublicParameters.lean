import NativeLargePublicOperations
import NativeSqrtMath

open Aeneas Std Result

namespace UdonVerify.LargePublicBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

abbrev Base := LargePublic.zakura_udon.field.pasta.parameters.PallasBase
abbrev Scalar := LargePublic.zakura_udon.field.pasta.parameters.PallasScalar
noncomputable abbrev fpSqrtInst :=
  LargePublic.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersPrimeModulus
noncomputable abbrev fqSqrtInst :=
  LargePublic.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersPrimeModulus

noncomputable def fpSqrtParameters : PastaParameters (Native.kernelInst (nativeModulus fpSqrtInst)) :=
  Native.transferParameters (Native.kernelInst (nativeModulus fpSqrtInst)) fpParameters
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

noncomputable def fqSqrtParameters : PastaParameters (Native.kernelInst (nativeModulus fqSqrtInst)) :=
  Native.transferParameters (Native.kernelInst (nativeModulus fqSqrtInst)) fqParameters
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

instance fpSqrtPrime : Fact (Nat.Prime (val4 fpSqrtParameters.modulus)) := ⟨Native.fp_prime⟩
instance fqSqrtPrime : Fact (Nat.Prime (val4 fqSqrtParameters.modulus)) := ⟨Native.fq_prime⟩
instance fpPrimeFact : Fact (Nat.Prime Native.fpPrime) := ⟨Native.fp_prime⟩
instance fqPrimeFact : Fact (Nat.Prime Native.fqPrime) := ⟨Native.fq_prime⟩

end UdonVerify.LargePublicBridge
