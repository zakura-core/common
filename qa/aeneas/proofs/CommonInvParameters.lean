import CommonSigned62Bounds
import CommonCoeffMath
import CommonCheckCompare

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

structure InvHelperParameters {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P) where
  modulus : Signed62
  mu : U64
  modulus_eq : inst.MODULUS_62 = ok modulus
  mu_eq : inst.MU = ok mu
  normalized : signed62Normalized modulus
  positive : 0 < signed62Value modulus
  bound : signed62Value modulus < 2 ^ 255
  inverse : Int.ModEq signedRadix (modulus[0]!.val * mu.val) 1
  sparse : modulus[2]!.val = 2 ∧ modulus[3]!.val = 0 ∧ modulus[4]!.val = 64

theorem inv_modulus_digit_bounds {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) :
    (∀ k : Fin 5, |params.modulus[k.val]!.val| ≤ signedRadix) ∧ |params.modulus[4]!.val| ≤ 256 := by
  apply signed62_small_value_bounds params.modulus params.normalized
  have hp := params.positive
  have hb := params.bound
  norm_num only at hb ⊢
  constructor <;> omega

theorem inv_coefficient_digit_bounds {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (a : Signed62) (hn : signed62Normalized a)
    (hr : -2 * signed62Value params.modulus < signed62Value a ∧
      signed62Value a < signed62Value params.modulus) :
    (∀ k : Fin 5, |a[k.val]!.val| ≤ signedRadix) ∧ |a[4]!.val| ≤ 256 := by
  apply signed62_small_value_bounds a hn
  have hp := params.positive
  have hb := params.bound
  norm_num only at hb ⊢
  constructor <;> omega

@[step]
theorem assert_coeff_range_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (a : Signed62) (what : Str)
    (hn : signed62Normalized a)
    (hr : -2 * signed62Value params.modulus < signed62Value a ∧
      signed62Value a < signed62Value params.modulus) :
    CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst a what ⦃ out => out = () ⦄ := by
  obtain ⟨ha, hta⟩ := inv_coefficient_digit_bounds inst params a hn hr
  obtain ⟨hm, htm⟩ := inv_modulus_digit_bounds inst params
  unfold CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range
  rw [params.modulus_eq]
  simp only [bind_ok]
  apply WP.spec_bind (check_mul_cmp_62_spec a 5#usize params.modulus (-2)#i64
    (by decide) (by decide) ha hm (by intro _; exact hta) htm)
  intro order horder
  have hfirst : IntegerCompareResult (signed62Value a) (-2 * signed62Value params.modulus) order := by
    simpa only [show (5#usize).val = 5 from by decide, active62_value_five,
      show ((-2)#i64).val = -2 from by decide] using horder
  have hgt : order = .gt := (integer_compare_tags _ _ order hfirst).2.2.mpr hr.1
  simp only [hgt, CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, bind_ok]
  apply WP.spec_bind (check_mul_cmp_62_spec a 5#usize params.modulus 1#i64
    (by decide) (by decide) ha hm (by intro _; exact hta) htm)
  intro order2 horder2
  have hsecond : IntegerCompareResult (signed62Value a) (signed62Value params.modulus) order2 := by
    simpa only [show (5#usize).val = 5 from by decide, active62_value_five,
      show (1#i64).val = 1 from by decide, one_mul] using horder2
  have hlt : order2 = .lt := (integer_compare_tags _ _ order2 hsecond).1.mpr hr.2
  simp [hlt, CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, WP.spec_ok]

#print axioms inv_modulus_digit_bounds
#print axioms inv_coefficient_digit_bounds
#print axioms assert_coeff_range_spec
end UdonVerify.CommonSigned62
