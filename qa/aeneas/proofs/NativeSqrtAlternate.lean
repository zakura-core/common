import NativeSqrtPublic

open Aeneas Std Result

namespace UdonVerify.SqrtNativeBridge
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem sqrt_alt_public_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    [Fact (Nat.Prime (val4 params.modulus))] (cfg : Configuration inst params inverse)
    (value : Element M Reduced) (hvalue : reducedValid (val4 params.modulus) value) :
    SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt_alt inst value ⦃ out =>
      sqrtAltResult (val4 params.modulus) inverse (fieldValue (val4 params.modulus) inverse value)
        (cfg.roots.value 32) out ⦄ := by
  unfold SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt_alt
  step -grind with (sqrt_is_zero_reduced inst params inverse cfg.inverse_mod value hvalue)
    as ⟨isZero, htest⟩
  split
  · rename_i hzero
    simp only [WP.spec_ok, sqrtAltResult, ↓reduceIte, mul_one]
    rcases sqrt_zero_reduced (M := M) (val4 params.modulus) inverse params.positive with ⟨hzValid, hzValue⟩
    refine ⟨hzValid, ?_, ?_⟩
    · simp only [hzValue, htest.mp hzero, zero_pow (by decide : (2 : Nat) ≠ 0)]
    · constructor
      · intro _; exact ⟨0, by simp only [htest.mp hzero, mul_zero]⟩
      · intro _; trivial
  · rename_i hnotZero
    have hnonzero : fieldValue (val4 params.modulus) inverse value ≠ 0 := by
      intro h; exact hnotZero (htest.mpr h)
    step -grind with (sqrt_widen_spec (val4 params.modulus) inverse value hvalue)
      as ⟨loose, hlooseValid, hlooseValue⟩
    step -grind with (cfg.power_spec loose hlooseValid) as ⟨w, hwValid, hwValue⟩
    have hvLoose : looseValid (val4 params.modulus) value := by
      change val4 value.limbs < 2 * val4 params.modulus
      change val4 value.limbs < val4 params.modulus at hvalue
      omega
    step -grind with (sqrt_multiply_spec inst params inverse cfg.inverse_mod value w hvLoose hwValid)
      as ⟨x, hxValid, hxValue⟩
    step -grind with (sqrt_multiply_spec inst params inverse cfg.inverse_mod x w hxValid hwValid)
      as ⟨t, htValid, htValue⟩
    apply finish_public_spec inst params inverse cfg _ hnonzero x t hxValid htValid
    · rw [hxValue, htValue, hxValue]
      ring
    · rw [htValue, hxValue, hwValue, hlooseValue]
      convert cfg.starting_power _ hnonzero using 1 <;> ring

@[step]
theorem sqrt_ratio_public_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse : Nat)
    [Fact (Nat.Prime (val4 params.modulus))] (cfg : Configuration inst params inverse)
    (num den : Element M Reduced) (hnum : reducedValid (val4 params.modulus) num)
    (hden : reducedValid (val4 params.modulus) den) :
    SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt_ratio inst num den ⦃ out =>
      sqrtRatioResult (val4 params.modulus) inverse (fieldValue (val4 params.modulus) inverse num)
        (fieldValue (val4 params.modulus) inverse den) (cfg.roots.value 32) out ⦄ := by
  unfold SqrtNative.zakura_udon.field.pasta.sqrt.PastaFieldMReduced.sqrt_ratio
  step -grind with (sqrt_is_zero_reduced inst params inverse cfg.inverse_mod num hnum)
    as ⟨numZero, hnumTest⟩
  split
  · rename_i hzero
    simp only [WP.spec_ok, sqrtRatioResult, hnumTest.mp hzero, ↓reduceIte]
    rcases sqrt_zero_reduced (M := M) (val4 params.modulus) inverse params.positive with ⟨hzValid, hzValue⟩
    exact ⟨hzValid, trivial, hzValue⟩
  · rename_i hnumNotZero
    have hn : fieldValue (val4 params.modulus) inverse num ≠ 0 := by
      intro h; exact hnumNotZero (hnumTest.mpr h)
    step -grind with (sqrt_is_zero_reduced inst params inverse cfg.inverse_mod den hden)
      as ⟨denZero, hdenTest⟩
    split
    · rename_i hzero
      simp only [WP.spec_ok, sqrtRatioResult, hn, hdenTest.mp hzero, ↓reduceIte]
      rcases sqrt_zero_reduced (M := M) (val4 params.modulus) inverse params.positive with ⟨hzValid, hzValue⟩
      exact ⟨hzValid, trivial, hzValue⟩
    · rename_i hdenNotZero
      have hd : fieldValue (val4 params.modulus) inverse den ≠ 0 := by
        intro h; exact hdenNotZero (hdenTest.mpr h)
      have hnLoose : looseValid (val4 params.modulus) num := by
        change val4 num.limbs < 2 * val4 params.modulus
        change val4 num.limbs < val4 params.modulus at hnum
        omega
      have hdLoose : looseValid (val4 params.modulus) den := by
        change val4 den.limbs < 2 * val4 params.modulus
        change val4 den.limbs < val4 params.modulus at hden
        omega
      step -grind with (sqrt_multiply_spec inst params inverse cfg.inverse_mod num den hnLoose hdLoose)
        as ⟨product, hpValid, hpValue⟩
      step -grind with (cfg.power_spec product hpValid) as ⟨w, hwValid, hwValue⟩
      step -grind with (sqrt_multiply_spec inst params inverse cfg.inverse_mod num w hnLoose hwValid)
        as ⟨x, hxValid, hxValue⟩
      step -grind with (sqrt_square_spec inst params inverse cfg.inverse_mod w hwValid)
        as ⟨wSquare, hwsValid, hwsValue⟩
      step -grind with (sqrt_multiply_spec inst params inverse cfg.inverse_mod product wSquare hpValid hwsValid)
        as ⟨t, htValid, htValue⟩
      have hequation : fieldValue (val4 params.modulus) inverse x ^ 2 =
          (fieldValue (val4 params.modulus) inverse num / fieldValue (val4 params.modulus) inverse den) *
            fieldValue (val4 params.modulus) inverse t := by
        rw [hxValue, htValue, hpValue, hwsValue]
        field_simp
        <;> ring
      have hpower : fieldValue (val4 params.modulus) inverse t ^ (2 ^ 32) = 1 := by
        rw [htValue, hwsValue, hwValue]
        exact cfg.starting_power _ (by rw [hpValue]; exact mul_ne_zero hn hd)
      step -grind with (finish_public_spec inst params inverse cfg
        (fieldValue (val4 params.modulus) inverse num / fieldValue (val4 params.modulus) inverse den)
        (div_ne_zero hn hd) x t hxValid htValid hequation hpower)
        as ⟨out, hout⟩
      rcases hout with ⟨houtValid, houtEquation, houtFlag⟩
      simp only [sqrtRatioResult, hn, hd, ↓reduceIte]
      refine ⟨houtValid, ?_, houtFlag⟩
      rw [houtEquation]
      rw [div_eq_mul_inv]
      calc
        (fieldValue (val4 params.modulus) inverse num *
          (fieldValue (val4 params.modulus) inverse den)⁻¹ *
          (if out.1 then 1 else cfg.roots.value 32)) * fieldValue (val4 params.modulus) inverse den =
            (fieldValue (val4 params.modulus) inverse num * (if out.1 then 1 else cfg.roots.value 32)) *
              ((fieldValue (val4 params.modulus) inverse den)⁻¹ * fieldValue (val4 params.modulus) inverse den) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hd, mul_one]

#print axioms sqrt_alt_public_spec
#print axioms sqrt_ratio_public_spec

end UdonVerify.SqrtNativeBridge
