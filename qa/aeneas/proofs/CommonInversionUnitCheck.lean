import CommonInversionInvariant
import CommonNormalizeCarry

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def one62 : Signed62 := make62 1#i64 0#i64 0#i64 0#i64 0#i64

theorem one62_value : signed62Value one62 = 1 := by
  norm_num [one62, make62, signed62Value]

theorem one62_digit_bounds : ∀ k : Fin 5, |one62[k.val]!.val| ≤ signedRadix := by
  intro k
  fin_cases k <;> norm_num [one62, make62, signedRadix]

def nativeUnitCheck {α : Type} (resume : α) (f : Signed62) (len : Usize) : Result α := do
  let order ← CommonInversion.field.pasta.safegcd.checks.mul_cmp_62 f len one62 1#i64
  let positive ← CommonInversion.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq order Ordering.eq
  if positive then ok resume else do
    let order ← CommonInversion.field.pasta.safegcd.checks.mul_cmp_62 f len one62 (-1)#i64
    let negative ← CommonInversion.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq order Ordering.eq
    massert negative
    ok resume

@[step]
theorem native_unit_check_spec {α P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (resume : α) (f : Signed62) (len : Usize)
    (hlen : 1 ≤ len.val ∧ len.val ≤ 5) (hn : active62Normalized f len.val)
    (hf : ∀ k : Fin 5, |f[k.val]!.val| ≤ signedRadix)
    (hunit : active62Value f len.val = 1 ∨ active62Value f len.val = -1) :
    nativeUnitCheck resume f len ⦃ out => out = resume ⦄ := by
  have hm : (1 : Int) < signed62Value params.helpers.modulus := by
    have := params.large
    norm_num only [signedRadix] at this
    omega
  have hfr : -signed62Value params.helpers.modulus < active62Value f len.val ∧
      active62Value f len.val ≤ signed62Value params.helpers.modulus := by
    rcases hunit with h | h <;> rw [h] <;> constructor <;> omega
  have htop := active62_modulus_top_bound params.helpers f len hn hfr
  unfold nativeUnitCheck
  rw [inversion_compare_bridge]
  apply WP.spec_bind (check_mul_cmp_62_spec f len one62 1#i64 hlen.2 (by decide) hf
    one62_digit_bounds htop (by norm_num [one62, make62]))
  intro order horder
  have hpos : IntegerCompareResult (active62Value f len.val) 1 order := by
    simpa only [one62_value, show (1#i64).val = 1 from by decide, one_mul] using horder
  rcases hunit with hunit | hunit
  · have heq : order = .eq := (integer_compare_tags _ _ order hpos).2.1.mpr hunit
    simp [heq, CommonInversion.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, WP.spec_ok]
  · have hlt : order = .lt := (integer_compare_tags _ _ order hpos).1.mpr (by omega)
    simp only [hlt, CommonInversion.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, bind_ok]
    simp
    rw [inversion_compare_bridge]
    apply WP.spec_bind (check_mul_cmp_62_spec f len one62 (-1)#i64 hlen.2 (by decide) hf
      one62_digit_bounds htop (by norm_num [one62, make62]))
    intro order2 horder2
    have hneg : IntegerCompareResult (active62Value f len.val) (-1) order2 := by
      simpa only [one62_value, show ((-1)#i64).val = -1 from by decide, mul_one] using horder2
    have heq : order2 = .eq := (integer_compare_tags _ _ order2 hneg).2.1.mpr hunit
    simp [heq, CommonInversion.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, massert, WP.spec_ok]

#print axioms one62_value
#print axioms one62_digit_bounds
#print axioms native_unit_check_spec
end UdonVerify.CommonSigned62
