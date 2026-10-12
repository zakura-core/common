import CommonInversionInvariant

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem inversion_initial_invariant {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (g : Signed62)
    (hn : signed62Normalized g) (hg : signed62Value g = x)
    (hx : 0 ≤ x ∧ x < signed62Value params.helpers.modulus) :
    InversionInvariant params x 0 params.helpers.modulus g zero62 params.r2 (-1)#i64 5#usize := by
  have hp := params.helpers.positive
  have hm := params.helpers.bound
  have hgRange : -2 * signed62Value params.helpers.modulus < signed62Value g ∧
      signed62Value g < signed62Value params.helpers.modulus := by rw [hg]; constructor <;> omega
  have hgd := (inv_coefficient_digit_bounds (inversionHelperDict inst) params.helpers g hn hgRange).1
  have hfd := (inv_modulus_digit_bounds (inversionHelperDict inst) params.helpers).1
  have hfCap : |active62Value params.helpers.modulus 5| ≤ signedRadix ^ 5 := by
    rw [active62_value_five, abs_of_pos hp]
    norm_num only [signedRadix] at hm ⊢
    omega
  have hgCap : |active62Value g 5| ≤ signedRadix ^ 5 := by
    rw [active62_value_five, hg, abs_of_nonneg hx.1]
    norm_num only [signedRadix] at hm ⊢
    omega
  exact {
    length := by decide
    f_value := by simp only [show (5#usize).val = 5 from by decide, active62_value_five,
      inversionTrace, Nat.mul_zero, iterate]
    g_value := by simp only [show (5#usize).val = 5 from by decide, active62_value_five,
      hg, inversionTrace, Nat.mul_zero, iterate]
    eta_value := by simp only [show ((-1)#i64).val = -1 from by decide, inversionTrace, Nat.mul_zero, iterate]
    f_normalized := by
      intro k hk
      change k.val + 1 < 5 at hk
      exact params.helpers.normalized ⟨k.val, by omega⟩
    g_normalized := by
      intro k hk
      change k.val + 1 < 5 at hk
      exact hn ⟨k.val, by omega⟩
    f_digits := hfd
    g_digits := hgd
    f_capacity := hfCap
    g_capacity := hgCap
    d_normalized := zero62_normalized
    e_normalized := params.r2_normalized
    d_range := by rw [zero62_value]; constructor <;> omega
    e_range := by have := params.r2_range; constructor <;> omega
    d_bezout := by
      change Int.ModEq (signed62Value params.helpers.modulus) (x * signed62Value zero62)
        (signed62Value params.r2 * active62Value params.helpers.modulus 5)
      rw [zero62_value, active62_value_five]
      simp [Int.ModEq]
    e_bezout := by
      change Int.ModEq (signed62Value params.helpers.modulus) (x * signed62Value params.r2)
        (signed62Value params.r2 * active62Value g 5)
      rw [active62_value_five, hg]
      simp [Int.ModEq, mul_comm] }

#print axioms inversion_initial_invariant
end UdonVerify.CommonSigned62
