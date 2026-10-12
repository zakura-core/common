import NativeSqrtParameters
import NativeSqrtChains

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def fpSqrtExponent : Nat := ((Native.fpPrime - 1) / 2 ^ 32 - 1) / 2
def fqSqrtExponent : Nat := ((Native.fqPrime - 1) / 2 ^ 32 - 1) / 2

@[step]
theorem fp_sqrt_power_spec (value : Element Base Loose) (hvalue : looseValid Native.fpPrime value) :
    fpSqrtInst.sealedParametersInst.pow_sqrt_exponent value ⦃ out =>
      looseValid Native.fpPrime out ∧ fieldValue Native.fpPrime Native.fpRadixInverse out =
        fieldValue Native.fpPrime Native.fpRadixInverse value ^ fpSqrtExponent ⦄ := by
  change SqrtNative.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.pow_sqrt_exponent value ⦃ out => _ ⦄
  unfold SqrtNative.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasBase.pow_sqrt_exponent
  step -grind with (Native.fp_pow_sqrt_exponent_spec { limbs := value.limbs, marker := () } hvalue)
    as ⟨out, houtBound, houtValue⟩
  refine ⟨houtBound, ?_⟩
  have h := congrArg (fun x : Nat => (x : ZMod Native.fpPrime)) houtValue
  simpa only [fieldValue, fpSqrtExponent, ZMod.natCast_mod, Nat.cast_pow] using h

@[step]
theorem fq_sqrt_power_spec (value : Element Scalar Loose) (hvalue : looseValid Native.fqPrime value) :
    fqSqrtInst.sealedParametersInst.pow_sqrt_exponent value ⦃ out =>
      looseValid Native.fqPrime out ∧ fieldValue Native.fqPrime Native.fqRadixInverse out =
        fieldValue Native.fqPrime Native.fqRadixInverse value ^ fqSqrtExponent ⦄ := by
  change SqrtNative.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.pow_sqrt_exponent value ⦃ out => _ ⦄
  unfold SqrtNative.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersSealedParametersPallasScalar.pow_sqrt_exponent
  step -grind with (Native.fq_pow_sqrt_exponent_spec { limbs := value.limbs, marker := () } hvalue)
    as ⟨out, houtBound, houtValue⟩
  refine ⟨houtBound, ?_⟩
  have h := congrArg (fun x : Nat => (x : ZMod Native.fqPrime)) houtValue
  simpa only [fieldValue, fqSqrtExponent, ZMod.natCast_mod, Nat.cast_pow] using h

theorem fp_sqrt_starting_power (a : ZMod Native.fpPrime) (ha : a ≠ 0) :
    (a * (a ^ fpSqrtExponent) ^ 2) ^ (2 ^ 32) = 1 := by
  apply Native.sqrt_initial_power _ _ _ Native.fp_prime
  · with_unfolding_all decide
  · exact ha

theorem fq_sqrt_starting_power (a : ZMod Native.fqPrime) (ha : a ≠ 0) :
    (a * (a ^ fqSqrtExponent) ^ 2) ^ (2 ^ 32) = 1 := by
  apply Native.sqrt_initial_power _ _ _ Native.fq_prime
  · with_unfolding_all decide
  · exact ha

#print axioms fp_sqrt_power_spec
#print axioms fq_sqrt_power_spec

end UdonVerify.SqrtNativeBridge
