import CommonInversionInvariant
import CommonActiveZero

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem inversion_fg_range_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (f g d e : Signed62)
    (eta : I64) (len : Usize) (hinv : InversionInvariant params x batches f g d e eta len)
    (hx : 0 ≤ x ∧ x < signed62Value params.helpers.modulus) :
    CommonInversion.field.pasta.safegcd.checks.assert_fg_range inst f g len ⦃ out => out = () ⦄ := by
  have hm := params.helpers.positive
  have hr := iterate_inversion_ranges (62 * batches) ⟨1, signed62Value params.helpers.modulus, x⟩
    (signed62Value params.helpers.modulus) hm params.odd
    (by constructor <;> constructor <;> dsimp <;> omega)
  rw [inversion_fg_range_bridge]
  apply assert_fg_range_spec (inversionHelperDict inst) params.helpers f g len hinv.length
    hinv.f_normalized hinv.g_normalized hinv.f_digits hinv.g_digits
  · simpa only [hinv.f_value, inversionTrace] using hr.1
  · simpa only [hinv.g_value, inversionTrace] using hr.2

@[step]
theorem inversion_is_zero_spec (g : Signed62) (len : Usize)
    (hlen : 1 ≤ len.val ∧ len.val ≤ 5) (hn : active62Normalized g len.val) :
    CommonInversion.field.pasta.safegcd.is_zero g len ⦃ out =>
      out = true ↔ active62Value g len.val = 0 ⦄ := by
  rw [inversion_zero_bridge]
  exact active_zero_spec g len hlen hn

#print axioms inversion_fg_range_spec
#print axioms inversion_is_zero_spec
end UdonVerify.CommonSigned62
