import NativeLargePublicConfig

open Aeneas Std Result

namespace UdonVerify.LargePublicBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem sqrt_public_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    [Fact (Nat.Prime (val4 params.modulus))] (cfg : Configuration inst params inverse)
    (value : Element M Reduced) (hvalue : reducedValid (val4 params.modulus) value) :
    LargePublic.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt inst value ⦃ out =>
      sqrtResult (val4 params.modulus) inverse (fieldValue (val4 params.modulus) inverse value) out ⦄ := by
  unfold LargePublic.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt
  step -grind with (sqrt_is_zero_reduced inst params inverse cfg.inverse_mod value hvalue)
    as ⟨isZero, htest⟩
  split
  · rename_i hzero
    simp only [WP.spec_ok, sqrtResult]
    rcases sqrt_zero_reduced (M := M) (val4 params.modulus) inverse params.positive with ⟨hzValid, hzValue⟩
    exact ⟨hzValid, by simp only [hzValue, htest.mp hzero, zero_pow (by decide : (2 : Nat) ≠ 0)]⟩
  · rename_i hnotZero
    have hnonzero : fieldValue (val4 params.modulus) inverse value ≠ 0 := by
      intro h; exact hnotZero (htest.mpr h)
    step -grind with (sqrt_widen_spec (val4 params.modulus) inverse value hvalue)
      as ⟨loose, hlooseValid, hlooseValue⟩
    step -grind with (cfg.power_spec loose hlooseValid) as ⟨w, hwValid, hwValue⟩
    apply cfg.sqrt_spec value hvalue hnonzero w hwValid
    rw [hwValue, hlooseValue]
    exact cfg.starting_power _ hnonzero

@[step]
theorem finish_public_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    [Fact (Nat.Prime (val4 params.modulus))] (cfg : Configuration inst params inverse)
    (a : ZMod (val4 params.modulus)) (ha : a ≠ 0)
    (x t : Element M Loose) (hx : looseValid (val4 params.modulus) x)
    (ht : looseValid (val4 params.modulus) t)
    (hequation : fieldValue (val4 params.modulus) inverse x ^ 2 =
      a * fieldValue (val4 params.modulus) inverse t)
    (hpower : fieldValue (val4 params.modulus) inverse t ^ (2 ^ 32) = 1) :
    LargePublic.zakura_udon.field.pasta.sqrt.finish inst x t ⦃ out =>
      sqrtAltResult (val4 params.modulus) inverse a cfg.topRoot out ⦄ := by
  unfold LargePublic.zakura_udon.field.pasta.sqrt.finish
  exact cfg.finish_spec a ha x t hx ht hequation hpower

#print axioms sqrt_public_spec
#print axioms finish_public_spec

end UdonVerify.LargePublicBridge
