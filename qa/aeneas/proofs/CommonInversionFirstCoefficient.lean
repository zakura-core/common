import CommonInversionContinue
import CommonInversionFirstFG

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem inversion_coeff_post_invariant {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (f g d e : Signed62)
    (eta : I64) (len : Usize) (hinv : InversionInvariant params x batches f g d e eta len)
    (fg : NativeFGOutput) (hfg : NativeFGPost params x batches len fg)
    (de : Signed62 × Signed62)
    (hde : CoeffUpdateResult params.helpers.modulus d e (inversionHelperMatrix fg.matrix) de) :
    InversionInvariant params x (batches + 1) fg.f fg.g de.1 de.2 fg.eta len := by
  have hodd : (inversionTrace (signed62Value params.helpers.modulus) x batches).f % 2 = 1 :=
    iterate_odd (62 * batches) _ params.odd
  obtain ⟨hrowF, hrowG, _, huv, hqr⟩ := native_batch_transition
    (inversionTrace (signed62Value params.helpers.modulus) x batches)
    (inversionDivstepMatrix fg.matrix, fg.eta) hfg.batch hodd
  change |fg.matrix.u.val| + |fg.matrix.v.val| ≤ signedRadix at huv
  change |fg.matrix.q.val| + |fg.matrix.r.val| ≤ signedRadix at hqr
  have hfRow : signedRadix * active62Value fg.f len.val =
      fg.matrix.u.val * active62Value f len.val + fg.matrix.v.val * active62Value g len.val := by
    simpa only [inversionDivstepMatrix, hfg.f_value, hinv.f_value, hinv.g_value, inversion_trace_next] using hrowF.symm
  have hgRow : signedRadix * active62Value fg.g len.val =
      fg.matrix.q.val * active62Value f len.val + fg.matrix.r.val * active62Value g len.val := by
    simpa only [inversionDivstepMatrix, hfg.g_value, hinv.f_value, hinv.g_value, inversion_trace_next] using hrowG.symm
  rcases hde with ⟨hnD, hnE, hrD, hrE, hmodD, hmodE⟩
  have hnewEta : fg.eta.val = -(inversionTrace (signed62Value params.helpers.modulus) x (batches + 1)).delta := by
    simpa only [inversion_trace_next] using hfg.batch.2.2.2.2
  exact {
    length := hinv.length
    f_value := hfg.f_value
    g_value := hfg.g_value
    eta_value := hnewEta
    f_normalized := hfg.f_normalized
    g_normalized := hfg.g_normalized
    f_digits := hfg.f_digits
    g_digits := hfg.g_digits
    f_capacity := hfg.f_capacity
    g_capacity := hfg.g_capacity
    d_normalized := hnD
    e_normalized := hnE
    d_range := hrD
    e_range := hrE
    d_bezout := coefficient_row_bezout params.helpers x (signed62Value params.r2)
      (active62Value f len.val) (active62Value g len.val) (signed62Value d) (signed62Value e)
      (active62Value fg.f len.val) (signed62Value de.1) fg.matrix.u.val fg.matrix.v.val
      hinv.d_bezout hinv.e_bezout hfRow hmodD
    e_bezout := coefficient_row_bezout params.helpers x (signed62Value params.r2)
      (active62Value f len.val) (active62Value g len.val) (signed62Value d) (signed62Value e)
      (active62Value fg.g len.val) (signed62Value de.2) fg.matrix.q.val fg.matrix.r.val
      hinv.d_bezout hinv.e_bezout hgRow hmodE }


@[step]
theorem native_first_coefficient_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (g : Signed62)
    (hinv : InversionInvariant params x 0 params.helpers.modulus g zero62 params.r2 (-1)#i64 5#usize)
    (fg : NativeFGOutput) (hfg : NativeFGPost params x 0 5#usize fg) :
    CommonInversion.field.pasta.safegcd.update_de_62_first inst params.r2 fg.matrix ⦃ de =>
      InversionInvariant params x 1 fg.f fg.g de.1 de.2 fg.eta 5#usize ⦄ := by
  have hodd : (inversionTrace (signed62Value params.helpers.modulus) x 0).f % 2 = 1 :=
    iterate_odd 0 _ params.odd
  obtain ⟨_, _, _, huv, hqr⟩ := native_batch_transition
    (inversionTrace (signed62Value params.helpers.modulus) x 0)
    (inversionDivstepMatrix fg.matrix, fg.eta) hfg.batch hodd
  rw [inversion_coeff_first_bridge]
  apply WP.spec_mono (update_de_62_first_spec (inversionHelperDict inst) params.helpers params.r2
    (inversionHelperMatrix fg.matrix) params.r2_normalized params.r2_range.1 hinv.e_range huv hqr)
  intro de hde
  exact inversion_coeff_post_invariant params x 0 _ _ _ _ _ _ hinv fg hfg de hde

#print axioms inversion_coeff_post_invariant
#print axioms native_first_coefficient_spec
end UdonVerify.CommonSigned62
