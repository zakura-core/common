import NativeSqrtConfig

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
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
    SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt inst value ⦃ out =>
      sqrtResult (val4 params.modulus) inverse (fieldValue (val4 params.modulus) inverse value) out ⦄ := by
  have h32 : (32#u32).val = 32 := by decide
  unfold SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt
  simp only [SqrtNative.zakura_udon.field.pasta.TWO_ADICITY]
  step -grind with (sqrt_is_zero_reduced inst params inverse cfg.inverse_mod value hvalue)
    as ⟨isZero, htest⟩
  split
  · rename_i hzero
    simp only [WP.spec_ok, sqrtResult]
    rcases sqrt_zero_reduced (M := M) (val4 params.modulus) inverse params.positive with ⟨hzValid, hzValue⟩
    exact ⟨hzValid, by simp only [hzValue, htest.mp hzero, zero_pow (by decide : (2 : Nat) ≠ 0)]⟩
  · rename_i hnotZero
    step -grind with (sqrt_widen_spec (val4 params.modulus) inverse value hvalue)
      as ⟨loose, hlooseValid, hlooseValue⟩
    step -grind with (cfg.power_spec loose hlooseValid) as ⟨w, hwValid, hwValue⟩
    rw [tonelli_bridge]
    step -grind with (Sqrt.tonelli_shanks_spec (sqrtInst inst) cfg.ops (sqrtCallback inst)
      () 32#u32 cfg.roots (by decide) (by decide) loose w
      ((cfg.valid_iff loose).mpr hlooseValid) ((cfg.valid_iff w).mpr hwValid)
      (by
        intro hnonzero
        rw [cfg.value_eq loose, cfg.value_eq w, hwValue, h32]
        exact cfg.starting_power _ (by simpa only [cfg.value_eq loose] using hnonzero))
      (by simpa only [h32] using cfg.nonsquare)) as ⟨root, hroot⟩
    unfold SqrtNative.core.option.Option.map
    cases root with
    | none =>
        simp only [WP.spec_ok, sqrtResult]
        simpa only [Sqrt.sqrtResult, cfg.value_eq loose, hlooseValue] using hroot
    | some root =>
        change (do
          let reduced ← SqrtNative.zakura_udon.field.pasta.PastaField.reduce inst looseInst root
          ok (some reduced)) ⦃ out => _ ⦄
        have hrootValid : looseValid (val4 params.modulus) root := (cfg.valid_iff root).mp hroot.1
        step -grind with (sqrt_reduce_spec inst params inverse root hrootValid)
          as ⟨reduced, hrValid, hrValue⟩
        simp only [sqrtResult]
        refine ⟨hrValid, ?_⟩
        rw [hrValue]
        simpa only [cfg.value_eq root, cfg.value_eq loose, hlooseValue] using hroot.2

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
    SqrtNative.zakura_udon.field.pasta.sqrt.finish inst x t ⦃ out =>
      sqrtAltResult (val4 params.modulus) inverse a (cfg.roots.value 32) out ⦄ := by
  have h32 : (32#u32).val = 32 := by decide
  unfold SqrtNative.zakura_udon.field.pasta.sqrt.finish
  simp only [SqrtNative.zakura_udon.field.pasta.TWO_ADICITY]
  rw [correction_bridge]
  step -grind with (Sqrt.correction_square_flag_spec (sqrtInst inst) cfg.ops (finishCallback inst)
    () 32#u32 (finishRoots cfg) (by decide) (by decide) a x t
    ((cfg.valid_iff x).mpr hx) ((cfg.valid_iff t).mpr ht)
    (by simpa only [cfg.value_eq x, cfg.value_eq t] using hequation)
    (by simpa only [cfg.value_eq t, h32] using hpower) ha
    (by simpa only [finishRoots, h32] using cfg.nonsquare))
    as ⟨isSquare, root, houtValid, houtEquation, houtFlag⟩
  step -grind with (sqrt_reduce_spec inst params inverse root ((cfg.valid_iff root).mp houtValid))
    as ⟨reduced, hrValid, hrValue⟩
  simp only [sqrtAltResult]
  refine ⟨hrValid, ?_, houtFlag⟩
  rw [hrValue]
  simpa only [cfg.value_eq root, finishRoots, h32] using houtEquation

#print axioms sqrt_public_spec
#print axioms finish_public_spec

end UdonVerify.SqrtNativeBridge
