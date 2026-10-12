import NativeLargeFinish

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def largeSqrtResult {M : Type} (p inverse : Nat) (a : ZMod p) :
    Option (Element M Reduced) → Prop
  | none => ¬ IsSquare a
  | some root => reducedValid p root ∧ fieldValue p inverse root ^ 2 = a

@[step]
theorem large_sqrt_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse root : Nat)
    [Fact (Nat.Prime (val4 params.modulus))]
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (table : Native.LargeTable M) (multiplier : U32)
    (hchecks : Native.largeProgressionChecks (val4 params.modulus) inverse root table)
    (hlookup : Native.largeInverseChecks (val4 params.modulus) multiplier.val table)
    (hroot : IsPrimitiveRoot (root : ZMod (val4 params.modulus)) (256 ^ 4))
    (hnonsquare : ¬ IsSquare (root : ZMod (val4 params.modulus)))
    (value : Element M Reduced) (hv : reducedValid (val4 params.modulus) value)
    (ha : fieldValue (val4 params.modulus) inverse value ≠ 0)
    (w : Element M Loose) (hw : looseValid (val4 params.modulus) w)
    (hpower : (fieldValue (val4 params.modulus) inverse value *
      fieldValue (val4 params.modulus) inverse w ^ 2) ^ (256 ^ 4) = 1) :
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.sqrt
      inst table value w multiplier ⦃ out =>
        largeSqrtResult (val4 params.modulus) inverse
          (fieldValue (val4 params.modulus) inverse value) out ⦄ := by
  unfold LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.sqrt
  step -grind with (large_multiply_spec inst params inverse hinverse value w
    (by unfold looseValid reducedValid at *; omega) hw) as ⟨x, hxBound, hxValue⟩
  step -grind with (large_multiply_spec inst params inverse hinverse x w hxBound hw)
    as ⟨t, htBound, htValue⟩
  have hsquare : fieldValue (val4 params.modulus) inverse x ^ 2 =
      fieldValue (val4 params.modulus) inverse value * fieldValue (val4 params.modulus) inverse t := by
    rw [hxValue, htValue, hxValue]
    ring
  have htPower : fieldValue (val4 params.modulus) inverse t ^ (256 ^ 4) = 1 := by
    have htEq : fieldValue (val4 params.modulus) inverse t =
        fieldValue (val4 params.modulus) inverse value * fieldValue (val4 params.modulus) inverse w ^ 2 := by
      rw [htValue, hxValue]
      ring
    rw [htEq]
    exact hpower
  step -grind with (large_finish_square_spec inst params inverse root hinverse table multiplier
    hchecks hlookup hroot hnonsquare (fieldValue (val4 params.modulus) inverse value) ha
    x t hxBound htBound hsquare htPower) as ⟨flag, candidate, hcBound, hcSquare, hflag⟩
  change (flag = true ↔ IsSquare (fieldValue (val4 params.modulus) inverse value)) at hflag
  unfold LargeAlgorithms.core.bool.Bool.then
  simp only [LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.sqrt.closure.Insts.CoreOpsFunctionFnOnceTuplePastaFieldMReduced,
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.sqrt.closure.Insts.CoreOpsFunctionFnOnceTuplePastaFieldMReduced.call_once]
  cases flag
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok, largeSqrtResult]
    intro hs
    have h := hflag.mpr hs
    exact Bool.noConfusion h
  · simp only [↓reduceIte]
    step -grind with (large_reduce_spec inst params inverse candidate hcBound)
      as ⟨canonical, hcanonicalBound, hcanonicalValue⟩
    try simp only [WP.spec_ok, largeSqrtResult]
    refine ⟨hcanonicalBound, ?_⟩
    rw [hcanonicalValue]
    simpa only [↓reduceIte, mul_one] using hcSquare

#print axioms large_sqrt_spec

end UdonVerify.LargeNativeBridge
