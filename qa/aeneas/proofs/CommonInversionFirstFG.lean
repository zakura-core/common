import CommonInversionInitial
import CommonInversionBatch

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def nativeInversionFirstFG {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (f g : Signed62) : Result NativeFGOutput := do
  let f0 ← Array.index_usize f 0#usize
  let g0 ← Array.index_usize g 0#usize
  let tm ← CommonInversion.field.pasta.safegcd.divsteps_62_var (-1)#i64 (IScalar.hcast .U64 f0) (IScalar.hcast .U64 g0)
  let fg ← CommonInversion.field.pasta.safegcd.update_fg_62_first inst f g tm.1
  ok ⟨tm.1, tm.2, fg.1, fg.2⟩

theorem native_first_fg_eq_generic {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (g : Signed62)
    (hinv : InversionInvariant params x 0 params.helpers.modulus g zero62 params.r2 (-1)#i64 5#usize) :
    nativeInversionFirstFG inst params.helpers.modulus g =
      nativeInversionBatch 5#usize params.helpers.modulus g (-1)#i64 := by
  let f := params.helpers.modulus
  have hfLow := (signed_cast_mod62 f[0]!).trans (signed62_low_congruence f).symm
  have hgLow := (signed_cast_mod62 g[0]!).trans (signed62_low_congruence g).symm
  obtain ⟨tm, htm, hbatch⟩ := WP.spec_imp_exists (inversion_divsteps_full_spec (-1)#i64
    (IScalar.hcast .U64 f[0]!) (IScalar.hcast .U64 g[0]!) (signed62Value f) (signed62Value g)
    (by norm_num [signedRadix]) params.odd hfLow hgLow)
  obtain ⟨hrowF, hrowG, _, huv, hqr⟩ := native_batch_transition
    ⟨-((-1)#i64).val, signed62Value f, signed62Value g⟩
    (inversionDivstepMatrix tm.1, tm.2) hbatch params.odd
  have hzeroF := inversion_row_low_zero f g 5 tm.1.u.val tm.1.v.val _ (by decide)
    (by simpa only [active62_value_five, inversionDivstepMatrix] using hrowF)
  have hzeroG := inversion_row_low_zero f g 5 tm.1.q.val tm.1.r.val _ (by decide)
    (by simpa only [active62_value_five, inversionDivstepMatrix] using hrowG)
  unfold nativeInversionFirstFG nativeInversionBatch
  rw [fg_index_eq f 0#usize (by decide), fg_index_eq g 0#usize (by decide)]
  simp only [bind_ok, show (0#usize).val = 0 from by decide]
  rw [htm]
  simp only [bind_ok]
  rw [inversion_fg_first_bridge, inversion_fg_update_bridge]
  rw [update_fg_62_first_eq_generic (inversionFirstDict inst) f g (inversionFirstMatrix tm.1)
    params.helpers.modulus_eq huv hqr params.helpers.sparse
    (by intro k _; exact hinv.f_digits k) (by intro k _; exact hinv.g_digits k) hzeroF hzeroG]
  rfl

@[step]
theorem native_first_fg_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (g : Signed62)
    (hinv : InversionInvariant params x 0 params.helpers.modulus g zero62 params.r2 (-1)#i64 5#usize) :
    nativeInversionFirstFG inst params.helpers.modulus g ⦃ out => NativeFGPost params x 0 5#usize out ⦄ := by
  rw [native_first_fg_eq_generic params x g hinv]
  exact native_inversion_batch_spec params x 0 _ _ _ _ _ _ (by decide) hinv

#print axioms native_first_fg_eq_generic
#print axioms native_first_fg_spec
end UdonVerify.CommonSigned62
