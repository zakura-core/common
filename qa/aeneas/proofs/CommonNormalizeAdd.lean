import CommonNormalizeCarry

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def normalizeAdd (r m : Signed62) : Result Signed62 := do
  let mask ← r[4]! >>> 63#i32
  let a0 ← r[0]! + (m[0]! &&& mask)
  let a1 ← r[1]! + (m[1]! &&& mask)
  let a2 ← r[2]! + (m[2]! &&& mask)
  let a3 ← r[3]! + (m[3]! &&& mask)
  let a4 ← r[4]! + (m[4]! &&& mask)
  ok (make62 a0 a1 a2 a3 a4)

@[step]
theorem normalize_add_spec {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (r : Signed62) (hn : signed62Normalized r)
    (hr : -2 * signed62Value params.modulus < signed62Value r ∧ signed62Value r < signed62Value params.modulus) :
    normalizeAdd r params.modulus ⦃ out =>
      signed62Value out = signed62Value r + (if signed62Value r < 0 then signed62Value params.modulus else 0) ∧
      (∀ k : Fin 4, 0 ≤ out[k.val]!.val ∧ out[k.val]!.val ≤ 2 * signedRadix - 2) ∧
      |out[4]!.val| ≤ 320 ⦄ := by
  obtain ⟨_, ht⟩ := inv_coefficient_digit_bounds inst params r hn hr
  have htRange := abs_le.mp ht
  have hs := signed62_sign_iff r hn
  have hsel (k : Fin 4) : 0 ≤ (params.modulus[k.val]! &&& signMask r[4]!).val ∧
      (params.modulus[k.val]! &&& signMask r[4]!).val < signedRadix := by
    rw [and_sign_mask_eq]
    split_ifs
    · exact params.normalized k
    · norm_num [signedRadix]
  unfold normalizeAdd
  step -grind with (signed_sign_mask_spec r[4]!) as ⟨mask, hmask⟩
  subst mask
  have hr0 := hn ⟨0, by decide⟩
  change 0 ≤ r[0]!.val ∧ r[0]!.val < signedRadix at hr0
  have hm0 := hsel ⟨0, by decide⟩
  change 0 ≤ (params.modulus[0]! &&& signMask r[4]!).val ∧
    (params.modulus[0]! &&& signMask r[4]!).val < signedRadix at hm0
  step -grind with (normalize_i64_add_spec r[0]! (params.modulus[0]! &&& signMask r[4]!) 0
    (2 * signedRadix - 2) (by omega) (by omega) (by norm_num [signedRadix])) as ⟨a0, ha0, ha0Lo, ha0Hi⟩
  have hr1 := hn ⟨1, by decide⟩
  change 0 ≤ r[1]!.val ∧ r[1]!.val < signedRadix at hr1
  have hm1 := hsel ⟨1, by decide⟩
  change 0 ≤ (params.modulus[1]! &&& signMask r[4]!).val ∧
    (params.modulus[1]! &&& signMask r[4]!).val < signedRadix at hm1
  step -grind with (normalize_i64_add_spec r[1]! (params.modulus[1]! &&& signMask r[4]!) 0
    (2 * signedRadix - 2) (by omega) (by omega) (by norm_num [signedRadix])) as ⟨a1, ha1, ha1Lo, ha1Hi⟩
  have hr2 := hn ⟨2, by decide⟩
  change 0 ≤ r[2]!.val ∧ r[2]!.val < signedRadix at hr2
  have hm2 := hsel ⟨2, by decide⟩
  change 0 ≤ (params.modulus[2]! &&& signMask r[4]!).val ∧
    (params.modulus[2]! &&& signMask r[4]!).val < signedRadix at hm2
  step -grind with (normalize_i64_add_spec r[2]! (params.modulus[2]! &&& signMask r[4]!) 0
    (2 * signedRadix - 2) (by omega) (by omega) (by norm_num [signedRadix])) as ⟨a2, ha2, ha2Lo, ha2Hi⟩
  have hr3 := hn ⟨3, by decide⟩
  change 0 ≤ r[3]!.val ∧ r[3]!.val < signedRadix at hr3
  have hm3 := hsel ⟨3, by decide⟩
  change 0 ≤ (params.modulus[3]! &&& signMask r[4]!).val ∧
    (params.modulus[3]! &&& signMask r[4]!).val < signedRadix at hm3
  step -grind with (normalize_i64_add_spec r[3]! (params.modulus[3]! &&& signMask r[4]!) 0
    (2 * signedRadix - 2) (by omega) (by omega) (by norm_num [signedRadix])) as ⟨a3, ha3, ha3Lo, ha3Hi⟩
  have hm4 : 0 ≤ (params.modulus[4]! &&& signMask r[4]!).val ∧
      (params.modulus[4]! &&& signMask r[4]!).val ≤ 64 := by
    rw [and_sign_mask_eq]
    split_ifs
    · simp only [params.sparse.2.2]
      decide
    · decide
  step -grind with (normalize_i64_add_spec r[4]! (params.modulus[4]! &&& signMask r[4]!) (-256) 320
    (by omega) (by omega) (by norm_num)) as ⟨a4, ha4, ha4Lo, ha4Hi⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, ?_⟩
  · by_cases hneg : r[4]!.val < 0
    · have hfull := hs.mpr hneg
      unfold signed62Value at hfull
      simp only [if_pos hfull, signed62Value, make62_get0, make62_get1, make62_get2,
        make62_get3, make62_get4, ha0, ha1, ha2, ha3, ha4, and_sign_mask_eq, if_pos hneg]
      ring
    · have hfull : ¬signed62Value r < 0 := by intro h; exact hneg (hs.mp h)
      unfold signed62Value at hfull
      simp only [if_neg hfull, signed62Value, make62_get0, make62_get1, make62_get2,
        make62_get3, make62_get4, ha0, ha1, ha2, ha3, ha4, and_sign_mask_eq, if_neg hneg,
        show (0#i64).val = 0 from by decide]
      ring
  · intro k
    fin_cases k
    · simpa only [make62_get0] using And.intro ha0Lo ha0Hi
    · simpa only [make62_get1] using And.intro ha1Lo ha1Hi
    · simpa only [make62_get2] using And.intro ha2Lo ha2Hi
    · simpa only [make62_get3] using And.intro ha3Lo ha3Hi
  · simp only [make62_get4, abs_le]
    constructor <;> omega

#print axioms normalize_add_spec
end UdonVerify.CommonSigned62
