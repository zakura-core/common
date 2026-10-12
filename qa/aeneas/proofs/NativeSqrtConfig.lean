import NativeSqrtRepresentation
import NativeSqrtPower
import NativeTonelliSqrt

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

/-- Every contract needed by the public methods, instantiated below for both Pasta fields. -/
structure Configuration {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    [Fact (Nat.Prime (val4 params.modulus))] where
  inverse_mod : Nat.ModEq (val4 params.modulus) (R * inverse) 1
  ops : Sqrt.Operations (K := ZMod (val4 params.modulus)) (sqrtInst inst)
  value_eq : ∀ x, ops.value x = fieldValue (val4 params.modulus) inverse x
  valid_iff : ∀ x, ops.valid x ↔ looseValid (val4 params.modulus) x
  roots : Sqrt.Roots ops (sqrtCallback inst) () 32#u32
  exponent : Nat
  power_spec : ∀ x, looseValid (val4 params.modulus) x →
    inst.sealedParametersInst.pow_sqrt_exponent x ⦃ out => looseValid (val4 params.modulus) out ∧
      fieldValue (val4 params.modulus) inverse out = fieldValue (val4 params.modulus) inverse x ^ exponent ⦄
  starting_power : ∀ a : ZMod (val4 params.modulus), a ≠ 0 → (a * (a ^ exponent) ^ 2) ^ (2 ^ 32) = 1
  nonsquare : ¬ IsSquare (roots.value 32)

def fpConfiguration : Configuration fpSqrtInst fpSqrtParameters Native.fpRadixInverse where
  inverse_mod := Native.fp_radix_inverse
  ops := fpOperations
  value_eq _ := rfl
  valid_iff _ := Iff.rfl
  roots := fpRootsContract
  exponent := fpSqrtExponent
  power_spec := fp_sqrt_power_spec
  starting_power := fp_sqrt_starting_power
  nonsquare := Native.fp_sqrt_nonsquare

def fqConfiguration : Configuration fqSqrtInst fqSqrtParameters Native.fqRadixInverse where
  inverse_mod := Native.fq_radix_inverse
  ops := fqOperations
  value_eq _ := rfl
  valid_iff _ := Iff.rfl
  roots := fqRootsContract
  exponent := fqSqrtExponent
  power_spec := fq_sqrt_power_spec
  starting_power := fq_sqrt_starting_power
  nonsquare := Native.fq_sqrt_nonsquare

def finishRoots {M : Type} {inst : Modulus M}
    {params : PastaParameters (Native.kernelInst (nativeModulus inst))} {inverse : Nat}
    [Fact (Nat.Prime (val4 params.modulus))] (cfg : Configuration inst params inverse) :
    Sqrt.Roots cfg.ops (finishCallback inst) () 32#u32 where
  value := cfg.roots.value
  lookup := by
    intro k hk hb
    rw [finish_callback_eq]
    exact cfg.roots.lookup k hk hb
  half_power := cfg.roots.half_power
  next_square := cfg.roots.next_square

def sqrtResult {M : Type} (p inverse : Nat) (a : ZMod p) (out : Option (Element M Reduced)) : Prop :=
  match out with
  | none => ¬ IsSquare a
  | some root => reducedValid p root ∧ fieldValue p inverse root ^ 2 = a

def sqrtAltResult {M : Type} (p inverse : Nat) (a topRoot : ZMod p)
    (out : Bool × Element M Reduced) : Prop :=
  reducedValid p out.2 ∧ fieldValue p inverse out.2 ^ 2 = a * (if out.1 then 1 else topRoot) ∧
    (out.1 = true ↔ IsSquare a)

def sqrtRatioResult {M : Type} (p inverse : Nat) [Fact (Nat.Prime p)] (num den topRoot : ZMod p)
    (out : Bool × Element M Reduced) : Prop :=
  reducedValid p out.2 ∧
    if num = 0 then out.1 = true ∧ fieldValue p inverse out.2 = 0
    else if den = 0 then out.1 = false ∧ fieldValue p inverse out.2 = 0
    else fieldValue p inverse out.2 ^ 2 * den = num * (if out.1 then 1 else topRoot) ∧
      (out.1 = true ↔ IsSquare (num / den))

#print axioms fpConfiguration
#print axioms fqConfiguration

end UdonVerify.SqrtNativeBridge
