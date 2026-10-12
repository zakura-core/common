import CommonNormalizeCarry

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post normalizeNegate

def normalizeNegateAll (r : Signed62) (sign : I64) : Result Signed62 := do
  let mask ← sign >>> 63#i32
  let a0 ← (r[0]! ^^^ mask) - mask
  let a1 ← (r[1]! ^^^ mask) - mask
  let a2 ← (r[2]! ^^^ mask) - mask
  let a3 ← (r[3]! ^^^ mask) - mask
  let a4 ← (r[4]! ^^^ mask) - mask
  ok (make62 a0 a1 a2 a3 a4)

@[step]
theorem normalize_negate_all_spec (r : Signed62) (sign : I64)
    (hr : ∀ k : Fin 4, 0 ≤ r[k.val]!.val ∧ r[k.val]!.val ≤ 2 * signedRadix - 2)
    (ht : |r[4]!.val| ≤ 320) :
    normalizeNegateAll r sign ⦃ out =>
      signed62Value out = (if sign.val < 0 then -signed62Value r else signed62Value r) ∧
      (∀ k : Fin 4, -2 * signedRadix + 2 ≤ out[k.val]!.val ∧ out[k.val]!.val ≤ 2 * signedRadix - 2) ∧
      |out[4]!.val| ≤ 320 ⦄ := by
  unfold normalizeNegateAll
  step -grind with (signed_sign_mask_spec sign) as ⟨mask, hmask⟩
  subst mask
  have hr0 := hr ⟨0, by decide⟩
  change 0 ≤ r[0]!.val ∧ r[0]!.val ≤ 2 * signedRadix - 2 at hr0
  step -grind with (normalize_negate_spec r[0]! sign
    (by norm_num only [signedRadix] at hr0 ⊢; constructor <;> omega)) as ⟨a0, ha0, ha0Lo, ha0Hi⟩
  have hr1 := hr ⟨1, by decide⟩
  change 0 ≤ r[1]!.val ∧ r[1]!.val ≤ 2 * signedRadix - 2 at hr1
  step -grind with (normalize_negate_spec r[1]! sign
    (by norm_num only [signedRadix] at hr1 ⊢; constructor <;> omega)) as ⟨a1, ha1, ha1Lo, ha1Hi⟩
  have hr2 := hr ⟨2, by decide⟩
  change 0 ≤ r[2]!.val ∧ r[2]!.val ≤ 2 * signedRadix - 2 at hr2
  step -grind with (normalize_negate_spec r[2]! sign
    (by norm_num only [signedRadix] at hr2 ⊢; constructor <;> omega)) as ⟨a2, ha2, ha2Lo, ha2Hi⟩
  have hr3 := hr ⟨3, by decide⟩
  change 0 ≤ r[3]!.val ∧ r[3]!.val ≤ 2 * signedRadix - 2 at hr3
  step -grind with (normalize_negate_spec r[3]! sign
    (by norm_num only [signedRadix] at hr3 ⊢; constructor <;> omega)) as ⟨a3, ha3, ha3Lo, ha3Hi⟩
  have htRange := abs_le.mp ht
  step -grind with (normalize_negate_spec r[4]! sign
    (by norm_num only [signedRadix]; constructor <;> omega)) as ⟨a4, ha4, ha4Lo, ha4Hi⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, ?_⟩
  · simp only [signed62Value, make62_get0, make62_get1, make62_get2, make62_get3, make62_get4,
      ha0, ha1, ha2, ha3, ha4]
    split_ifs <;> ring
  · intro k
    fin_cases k
    · simpa only [make62_get0] using And.intro ha0Lo ha0Hi
    · simpa only [make62_get1] using And.intro ha1Lo ha1Hi
    · simpa only [make62_get2] using And.intro ha2Lo ha2Hi
    · simpa only [make62_get3] using And.intro ha3Lo ha3Hi
  · simp only [make62_get4]
    rw [ha4]
    split_ifs
    · rwa [abs_neg]
    · exact ht

#print axioms normalize_negate_all_spec
end UdonVerify.CommonSigned62
