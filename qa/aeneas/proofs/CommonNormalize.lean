import CommonNormalizeCompose

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem normalize_62_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (r : Signed62) (sign : I64)
    (hn : signed62Normalized r)
    (hr : -2 * signed62Value params.modulus < signed62Value r ∧ signed62Value r < signed62Value params.modulus) :
    CommonInvHelpers.field.pasta.safegcd.normalize_62 inst r sign ⦃ out =>
      signed62Normalized out ∧
      (0 ≤ signed62Value out ∧ signed62Value out < signed62Value params.modulus) ∧
      Int.ModEq (signed62Value params.modulus) (signed62Value out)
        (if sign.val < 0 then -signed62Value r else signed62Value r) ⦄ := by
  rw [normalize_columns_bridge params]
  unfold normalizeColumns
  rw [fg_result_eq (assert_coeff_range_spec inst params r (CommonInvHelpers.toStr "normalize input") hn hr)]
  simp only [bind_ok]
  apply WP.spec_bind (normalize_add_spec params r hn hr)
  intro a ha
  rcases ha with ⟨haValue, haLow, haTop⟩
  have haRange : -signed62Value params.modulus < signed62Value a ∧
      signed62Value a < signed62Value params.modulus := by
    rw [haValue]
    exact normalize_first_range _ _ params.positive hr
  have haMod := normalize_add_congruence (signed62Value r) (signed62Value params.modulus)
  rw [← haValue] at haMod
  apply WP.spec_bind (normalize_negate_all_spec a sign haLow haTop)
  intro n hnOut
  rcases hnOut with ⟨hnValue, hnLow, hnTop⟩
  have hnRange : -signed62Value params.modulus < signed62Value n ∧
      signed62Value n < signed62Value params.modulus := by
    rw [hnValue]
    exact normalize_signed_range _ _ haRange (sign.val < 0)
  have hnMod : Int.ModEq (signed62Value params.modulus) (signed62Value n)
      (if sign.val < 0 then -signed62Value r else signed62Value r) := by
    rw [hnValue]
    split_ifs
    · exact haMod.neg
    · exact haMod
  apply WP.spec_bind (normalize_carry_spec n hnLow (by omega))
  intro c hc
  rcases hc with ⟨hcNormal, hcValue, hcTop⟩
  have hcRange : -2 * signed62Value params.modulus < signed62Value c ∧
      signed62Value c < signed62Value params.modulus := by
    have := params.positive
    rw [hcValue]
    constructor <;> omega
  apply WP.spec_bind (normalize_add_spec params c hcNormal hcRange)
  intro a2 ha2
  rcases ha2 with ⟨ha2Value, ha2Low, ha2Top⟩
  have ha2Range : 0 ≤ signed62Value a2 ∧ signed62Value a2 < signed62Value params.modulus := by
    rw [ha2Value, hcValue]
    exact normalize_final_range _ _ params.positive hnRange
  have ha2Mod := normalize_add_congruence (signed62Value c) (signed62Value params.modulus)
  rw [← ha2Value, hcValue] at ha2Mod
  have ha2CarryLow : ∀ k : Fin 4, -2 * signedRadix + 2 ≤ a2[k.val]!.val ∧
      a2[k.val]!.val ≤ 2 * signedRadix - 2 := by
    intro k
    have h := ha2Low k
    norm_num only [signedRadix] at h ⊢
    constructor <;> omega
  apply WP.spec_bind (normalize_carry_spec a2 ha2CarryLow (by omega))
  intro out hout
  rcases hout with ⟨houtNormal, houtValue, houtTop⟩
  have houtRange : 0 ≤ signed62Value out ∧ signed62Value out < signed62Value params.modulus := by
    rwa [houtValue]
  have houtCoeffRange : -2 * signed62Value params.modulus < signed62Value out ∧
      signed62Value out < signed62Value params.modulus := by
    have := params.positive
    constructor <;> omega
  have houtMod : Int.ModEq (signed62Value params.modulus) (signed62Value out)
      (if sign.val < 0 then -signed62Value r else signed62Value r) := by
    rw [houtValue]
    exact ha2Mod.trans hnMod
  rw [fg_result_eq (normalize_canonical_check_spec out (normalize_canonical_digits params out houtNormal houtRange)),
    fg_result_eq (first_coeff_input_check_spec params out houtNormal houtRange.1 houtCoeffRange),
    fg_result_eq (normalize_reduced_check_spec params out houtNormal houtRange)]
  simp only [bind_ok, WP.spec_ok]
  exact ⟨houtNormal, houtRange, houtMod⟩

#print axioms normalize_62_spec
end UdonVerify.CommonSigned62
