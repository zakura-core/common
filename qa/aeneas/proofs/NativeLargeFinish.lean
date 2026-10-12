import NativeLargeRecovery

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem large_finish_exponent_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse root : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (table : Native.LargeTable M) (multiplier : U32)
    (hchecks : Native.largeProgressionChecks (val4 params.modulus) inverse root table)
    (hlookup : Native.largeInverseChecks (val4 params.modulus) multiplier.val table)
    (hroot : (root : ZMod (val4 params.modulus)) ^ (256 ^ 4) = 1)
    (x t : Element M Loose) (hx : looseValid (val4 params.modulus) x)
    (ht : looseValid (val4 params.modulus) t)
    (exponent : Nat) (hexponent : exponent < 256 ^ 4)
    (hcorrect : fieldValue (val4 params.modulus) inverse t *
      (root : ZMod (val4 params.modulus)) ^ exponent = 1) :
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish
      inst table x t multiplier ⦃ out =>
        out.1 = decide (exponent % 2 = 0) ∧ looseValid (val4 params.modulus) out.2 ∧
        fieldValue (val4 params.modulus) inverse out.2 =
          fieldValue (val4 params.modulus) inverse x *
            (root : ZMod (val4 params.modulus)) ^ ((exponent + 1) / 2) ⦄ := by
  rw [large_finish_bridge]
  step -grind with (large_recover_spec inst params inverse root hinverse table multiplier
    hchecks hlookup hroot t ht exponent hexponent hcorrect) as ⟨e, he⟩
  simpa only [he] using large_correct_spec inst params inverse root hinverse table hchecks x hx e

@[step]
theorem large_finish_square_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse root : Nat)
    [Fact (Nat.Prime (val4 params.modulus))]
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (table : Native.LargeTable M) (multiplier : U32)
    (hchecks : Native.largeProgressionChecks (val4 params.modulus) inverse root table)
    (hlookup : Native.largeInverseChecks (val4 params.modulus) multiplier.val table)
    (hroot : IsPrimitiveRoot (root : ZMod (val4 params.modulus)) (256 ^ 4))
    (hnonsquare : ¬ IsSquare (root : ZMod (val4 params.modulus)))
    (a : ZMod (val4 params.modulus)) (ha : a ≠ 0)
    (x t : Element M Loose) (hx : looseValid (val4 params.modulus) x)
    (ht : looseValid (val4 params.modulus) t)
    (hsquare : fieldValue (val4 params.modulus) inverse x ^ 2 =
      a * fieldValue (val4 params.modulus) inverse t)
    (hpower : fieldValue (val4 params.modulus) inverse t ^ (256 ^ 4) = 1) :
    LargeAlgorithms.zakura_udon.field.pasta.sqrt.large.LargeSqrtTablePastaFieldMReduced.finish
      inst table x t multiplier ⦃ out =>
        looseValid (val4 params.modulus) out.2 ∧
        fieldValue (val4 params.modulus) inverse out.2 ^ 2 =
          a * (if out.1 then 1 else (root : ZMod (val4 params.modulus))) ∧
        (out.1 = true ↔ IsSquare a) ⦄ := by
  obtain ⟨exponent, hexponent, hcorrect⟩ := LargeSqrt.inverse_exponent_exists
    (root : ZMod (val4 params.modulus)) (fieldValue (val4 params.modulus) inverse t) hroot hpower
  step -grind with (large_finish_exponent_spec inst params inverse root hinverse table multiplier
    hchecks hlookup hroot.pow_eq_one x t hx ht exponent hexponent hcorrect)
    as ⟨out, hflag, hcBound, hcValue⟩
  rcases out with ⟨flag, candidate⟩
  change flag = decide (exponent % 2 = 0) at hflag
  have hexponent32 : exponent < 2 ^ 32 := by norm_num at hexponent ⊢; exact hexponent
  have hcandidate : fieldValue (val4 params.modulus) inverse candidate ^ 2 =
      a * (root : ZMod (val4 params.modulus)) ^ (exponent % 2) := by
    rw [hcValue]
    exact LargeSqrt.candidate_square a (fieldValue (val4 params.modulus) inverse t)
      (fieldValue (val4 params.modulus) inverse x) (root : ZMod (val4 params.modulus))
      exponent hexponent32 hsquare hcorrect
  have hparity : (root : ZMod (val4 params.modulus)) ^ (exponent % 2) =
      if flag then 1 else (root : ZMod (val4 params.modulus)) := by
    rw [hflag]
    by_cases hz : exponent % 2 = 0
    · simp [hz]
    · have ho : exponent % 2 = 1 := by omega
      simp [hz, ho]
  have hequation := hcandidate.trans (congrArg (fun value => a * value) hparity)
  exact ⟨hcBound, hequation,
    Sqrt.square_flag_correct a (root : ZMod (val4 params.modulus))
      (fieldValue (val4 params.modulus) inverse candidate) flag ha hnonsquare hequation⟩

#print axioms large_finish_exponent_spec
#print axioms large_finish_square_spec

end UdonVerify.LargeNativeBridge
