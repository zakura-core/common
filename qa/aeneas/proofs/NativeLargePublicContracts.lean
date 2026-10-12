import NativeLargePublicRepresentation
import NativeLargePublicPower

open Aeneas Std Result

namespace UdonVerify.LargePublicBridge
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

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

/-- Contracts for the feature-selected callbacks and the shared exponentiation schedule. -/
structure Configuration {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    [Fact (Nat.Prime (val4 params.modulus))] where
  inverse_mod : Nat.ModEq (val4 params.modulus) (R * inverse) 1
  exponent : Nat
  topRoot : ZMod (val4 params.modulus)
  power_spec : ∀ x, looseValid (val4 params.modulus) x →
    inst.sealedParametersInst.pow_sqrt_exponent x ⦃ out => looseValid (val4 params.modulus) out ∧
      fieldValue (val4 params.modulus) inverse out = fieldValue (val4 params.modulus) inverse x ^ exponent ⦄
  starting_power : ∀ a : ZMod (val4 params.modulus), a ≠ 0 → (a * (a ^ exponent) ^ 2) ^ (2 ^ 32) = 1
  sqrt_spec : ∀ value : Element M Reduced, reducedValid (val4 params.modulus) value →
    fieldValue (val4 params.modulus) inverse value ≠ 0 →
    ∀ w : Element M Loose, looseValid (val4 params.modulus) w →
    (fieldValue (val4 params.modulus) inverse value * fieldValue (val4 params.modulus) inverse w ^ 2) ^ (2 ^ 32) = 1 →
    inst.sealedParametersInst.sqrt_large value w ⦃ out =>
      sqrtResult (val4 params.modulus) inverse (fieldValue (val4 params.modulus) inverse value) out ⦄
  finish_spec : ∀ a : ZMod (val4 params.modulus), a ≠ 0 →
    ∀ x t : Element M Loose, looseValid (val4 params.modulus) x → looseValid (val4 params.modulus) t →
    fieldValue (val4 params.modulus) inverse x ^ 2 = a * fieldValue (val4 params.modulus) inverse t →
    fieldValue (val4 params.modulus) inverse t ^ (2 ^ 32) = 1 →
    inst.sealedParametersInst.sqrt_finish_large x t ⦃ out =>
      sqrtAltResult (val4 params.modulus) inverse a topRoot out ⦄

end UdonVerify.LargePublicBridge
