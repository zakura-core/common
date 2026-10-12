import CommonNormalizeMath
import CommonCoeffFirstCompose

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def normalizeCanonicalCheck (r : Signed62) : Result Unit := do
  let s0 ← r[0]! >>> 62#i32
  massert (s0 = 0#i64)
  let s1 ← r[1]! >>> 62#i32
  massert (s1 = 0#i64)
  let s2 ← r[2]! >>> 62#i32
  massert (s2 = 0#i64)
  let s3 ← r[3]! >>> 62#i32
  massert (s3 = 0#i64)
  let s4 ← r[4]! >>> 62#i32
  massert (s4 = 0#i64)

@[step]
theorem normalize_canonical_check_spec (r : Signed62)
    (hr : ∀ k : Fin 5, 0 ≤ r[k.val]!.val ∧ r[k.val]!.val < signedRadix) :
    normalizeCanonicalCheck r ⦃ out => out = () ⦄ := by
  unfold normalizeCanonicalCheck
  rw [signed62_low_shift_eq _ (hr ⟨0, by decide⟩)]
  simp only [bind_ok, massert, ite_true]
  rw [signed62_low_shift_eq _ (hr ⟨1, by decide⟩)]
  simp only [bind_ok, massert, ite_true]
  rw [signed62_low_shift_eq _ (hr ⟨2, by decide⟩)]
  simp only [bind_ok, massert, ite_true]
  rw [signed62_low_shift_eq _ (hr ⟨3, by decide⟩)]
  simp only [bind_ok, massert, ite_true]
  rw [signed62_low_shift_eq _ (hr ⟨4, by decide⟩)]
  simp [bind_ok, massert, WP.spec_ok]

def normalizeReducedCheck (r m : Signed62) : Result Unit := do
  let order ← CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62 r 5#usize m 1#i64
  let reduced ← CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq order Ordering.lt
  massert reduced

@[step]
theorem normalize_reduced_check_spec {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (r : Signed62) (hn : signed62Normalized r)
    (hr : 0 ≤ signed62Value r ∧ signed62Value r < signed62Value params.modulus) :
    normalizeReducedCheck r params.modulus ⦃ out => out = () ⦄ := by
  have hrange : -2 * signed62Value params.modulus < signed62Value r ∧
      signed62Value r < signed62Value params.modulus := by
    have := params.positive
    constructor <;> omega
  obtain ⟨hd, ht⟩ := inv_coefficient_digit_bounds inst params r hn hrange
  obtain ⟨hm, hmt⟩ := inv_modulus_digit_bounds inst params
  unfold normalizeReducedCheck
  apply WP.spec_bind (check_mul_cmp_62_spec r 5#usize params.modulus 1#i64 (by decide) (by decide)
    hd hm (by intro _; exact ht) hmt)
  intro order horder
  have hcompare : IntegerCompareResult (signed62Value r) (signed62Value params.modulus) order := by
    simpa only [show (5#usize).val = 5 from by decide, active62_value_five,
      show (1#i64).val = 1 from by decide, one_mul] using horder
  have hlt : order = .lt := (integer_compare_tags _ _ order hcompare).1.mpr hr.2
  simp [hlt, CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, massert, WP.spec_ok]

#print axioms normalize_canonical_check_spec
#print axioms normalize_reduced_check_spec
end UdonVerify.CommonSigned62
