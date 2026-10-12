import CommonCheckCompareLoop
import CommonCheckNormalize

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def IntegerCompareResult (left right : Int) : Ordering → Prop
  | .lt => left < right
  | .eq => left = right
  | .gt => right < left

theorem integer_compare_tags (left right : Int) (out : Ordering)
    (h : IntegerCompareResult left right out) :
    (out = .lt ↔ left < right) ∧ (out = .eq ↔ left = right) ∧ (out = .gt ↔ right < left) := by
  cases out <;> dsimp only [IntegerCompareResult] at h <;> simp_all <;> omega

@[step]
theorem check_mul_cmp_62_spec (a : Signed62) (alen : Usize) (b : Signed62) (factor : I64)
    (hlen : alen.val ≤ 5) (hf : |factor.val| ≤ 2)
    (ha : ∀ k : Fin 5, |a[k.val]!.val| ≤ signedRadix)
    (hb : ∀ k : Fin 5, |b[k.val]!.val| ≤ signedRadix)
    (hta : alen.val = 5 → |a[4]!.val| ≤ 256) (htb : |b[4]!.val| ≤ 256) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62 a alen b factor ⦃ out =>
      IntegerCompareResult (active62Value a alen.val) (factor.val * signed62Value b) out ⦄ := by
  unfold CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62
  apply WP.spec_bind (check_mul_62_spec a alen 1#i64 hlen (by decide) ha hta)
  intro am ham
  apply WP.spec_bind (check_mul_62_spec b 5#usize factor (by decide) hf hb (by intro _; exact htb))
  intro bm hbm
  apply WP.spec_bind (check_normalize_loop_spec am bm ham.1 hbm.1
    { start := 0#usize, «end» := 4#usize } (by decide) rfl)
  intro normalized hnormalized
  subst normalized
  simp only [Std.uncurry_apply_pair, core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_ok]
  apply WP.spec_mono (check_compare_loop_spec am bm ham.1 hbm.1 5#usize (by decide)
    (by intro j hj; have := j.isLt; change 5 ≤ j.val at hj; omega))
  intro out hcompare
  have hva : signed62Value am = active62Value a alen.val := by
    have h := ham.2
    rwa [show (1#i64).val = 1 from by decide, one_mul] at h
  have hvb : signed62Value bm = factor.val * signed62Value b := by
    have h := hbm.2
    simpa only [show (5#usize).val = 5 from by decide, active62_value_five] using h
  cases out <;> simpa only [CheckCompareResult, IntegerCompareResult, hva, hvb] using hcompare

#print axioms integer_compare_tags
#print axioms check_mul_cmp_62_spec
end UdonVerify.CommonSigned62
