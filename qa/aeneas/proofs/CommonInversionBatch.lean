import CommonInversionInvariant
import CommonInversionFGMath

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

structure NativeFGOutput where
  matrix : CommonInversion.field.pasta.safegcd.Trans2x2
  eta : I64
  f : Signed62
  g : Signed62

def nativeInversionBatch (len : Usize) (f g : Signed62) (eta : I64) : Result NativeFGOutput := do
  let f0 ← Array.index_usize f 0#usize
  let g0 ← Array.index_usize g 0#usize
  let tm ← CommonInversion.field.pasta.safegcd.divsteps_62_var eta (IScalar.hcast .U64 f0) (IScalar.hcast .U64 g0)
  let fg ← CommonInversion.field.pasta.safegcd.update_fg_62_var len f g tm.1
  ok ⟨tm.1, tm.2, fg.1, fg.2⟩

structure NativeFGPost {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (len : Usize)
    (out : NativeFGOutput) : Prop where
  batch : NativeBatchResult (inversionTrace (signed62Value params.helpers.modulus) x batches)
    (inversionDivstepMatrix out.matrix, out.eta)
  f_value : active62Value out.f len.val = (inversionTrace (signed62Value params.helpers.modulus) x (batches + 1)).f
  g_value : active62Value out.g len.val = (inversionTrace (signed62Value params.helpers.modulus) x (batches + 1)).g
  f_normalized : active62Normalized out.f len.val
  g_normalized : active62Normalized out.g len.val
  f_digits : ∀ k : Fin 5, |out.f[k.val]!.val| ≤ signedRadix
  g_digits : ∀ k : Fin 5, |out.g[k.val]!.val| ≤ signedRadix
  f_capacity : |active62Value out.f len.val| ≤ signedRadix ^ len.val
  g_capacity : |active62Value out.g len.val| ≤ signedRadix ^ len.val

@[step]
theorem native_inversion_batch_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (f g d e : Signed62)
    (eta : I64) (len : Usize) (hb : batches ≤ 11)
    (hinv : InversionInvariant params x batches f g d e eta len) :
    nativeInversionBatch len f g eta ⦃ out => NativeFGPost params x batches len out ⦄ := by
  let current := inversionTrace (signed62Value params.helpers.modulus) x batches
  have hfOdd : active62Value f len.val % 2 = 1 := by
    rw [hinv.f_value]
    exact iterate_odd (62 * batches) _ params.odd
  have hstate : (⟨-eta.val, active62Value f len.val, active62Value g len.val⟩ : State) = current := by
    rw [hinv.eta_value, hinv.f_value, hinv.g_value, neg_neg]
  have hEta : |eta.val| ≤ 683 := by
    rw [hinv.eta_value, abs_neg]
    exact inversion_trace_eta_bound _ _ _ hb
  have hfLow := (signed_cast_mod62 f[0]!).trans (active62_low_congruence f len.val hinv.length).symm
  have hgLow := (signed_cast_mod62 g[0]!).trans (active62_low_congruence g len.val hinv.length).symm
  unfold nativeInversionBatch
  rw [fg_index_eq f 0#usize (by decide), fg_index_eq g 0#usize (by decide)]
  simp only [bind_ok]
  apply WP.spec_bind (inversion_divsteps_full_spec eta (IScalar.hcast .U64 f[0]!)
    (IScalar.hcast .U64 g[0]!) _ _ hEta hfOdd hfLow hgLow)
  intro tm htm
  rw [hstate] at htm
  have hcurrentOdd : current.f % 2 = 1 := iterate_odd (62 * batches) _ params.odd
  obtain ⟨hrowF, hrowG, hdet, huv, hqr⟩ := native_batch_transition current
    (inversionDivstepMatrix tm.1, tm.2) htm hcurrentOdd
  have hrowFLocal : tm.1.u.val * active62Value f len.val + tm.1.v.val * active62Value g len.val =
      signedRadix * (iterate 62 current).f := by simpa only [inversionDivstepMatrix, current, hinv.f_value, hinv.g_value] using hrowF
  have hrowGLocal : tm.1.q.val * active62Value f len.val + tm.1.r.val * active62Value g len.val =
      signedRadix * (iterate 62 current).g := by simpa only [inversionDivstepMatrix, current, hinv.f_value, hinv.g_value] using hrowG
  have hzeroF := inversion_row_low_zero f g len.val tm.1.u.val tm.1.v.val _ hinv.length hrowFLocal
  have hzeroG := inversion_row_low_zero f g len.val tm.1.q.val tm.1.r.val _ hinv.length hrowGLocal
  rw [inversion_fg_update_bridge]
  apply WP.spec_bind (update_fg_62_var_spec len f g (inversionFGMatrix tm.1) hinv.length huv hqr
    (by intro k _; exact hinv.f_digits k) (by intro k _; exact hinv.g_digits k) hzeroF hzeroG)
  intro fg hfg
  rcases hfg with ⟨hvalueF, hvalueG, hnormal, hinactive⟩
  have hfNext : active62Value fg.1 len.val = (iterate 62 current).f :=
    inversion_scaled_eq _ _ (hvalueF.trans hrowFLocal)
  have hgNext : active62Value fg.2 len.val = (iterate 62 current).g :=
    inversion_scaled_eq _ _ (hvalueG.trans hrowGLocal)
  have hcap := iterate_bound 62 current (signedRadix ^ len.val) (by exact _root_.le_of_lt (pow_pos (by norm_num [signedRadix]) _)) hcurrentOdd
    (by simpa only [hinv.f_value] using hinv.f_capacity) (by simpa only [hinv.g_value] using hinv.g_capacity)
  have hfCap : |active62Value fg.1 len.val| ≤ signedRadix ^ len.val := by rw [hfNext]; exact hcap.1
  have hgCap : |active62Value fg.2 len.val| ≤ signedRadix ^ len.val := by rw [hgNext]; exact hcap.2
  have hfNormal : active62Normalized fg.1 len.val := by intro k hk; exact (hnormal k hk).1
  have hgNormal : active62Normalized fg.2 len.val := by intro k hk; exact (hnormal k hk).2
  have hfDigits := inversion_all_digit_bounds f fg.1 len.val hinv.length hfNormal hfCap
    (by intro k hk; exact (hinactive k hk).1) hinv.f_digits
  have hgDigits := inversion_all_digit_bounds g fg.2 len.val hinv.length hgNormal hgCap
    (by intro k hk; exact (hinactive k hk).2) hinv.g_digits
  simp only [WP.spec_ok]
  exact ⟨htm, by simpa only [inversion_trace_next] using hfNext,
    by simpa only [inversion_trace_next] using hgNext, hfNormal, hgNormal, hfDigits, hgDigits, hfCap, hgCap⟩

#print axioms native_inversion_batch_spec
end UdonVerify.CommonSigned62
