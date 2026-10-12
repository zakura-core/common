import CommonInversionFirstCoefficient
import CommonInversionChecks

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

structure InversionReady where
  f : Signed62
  g : Signed62
  d : Signed62
  e : Signed62
  eta : I64
  len : Usize

def nativeInversionFirst {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (modulus g r2 : Signed62) : Result InversionReady := do
  let fg ← nativeInversionFirstFG inst modulus g
  let zero ← CommonInversion.field.pasta.safegcd.is_zero fg.g 5#usize
  massert (¬ zero)
  let (d, e) ← CommonInversion.field.pasta.safegcd.update_de_62_first inst r2 fg.matrix
  CommonInversion.field.pasta.safegcd.checks.assert_fg_range inst fg.f fg.g 5#usize
  let (f1, g1, len) ← CommonInversion.field.pasta.safegcd.shrink_len fg.f fg.g 5#usize
  ok ⟨f1, g1, d, e, fg.eta, len⟩

@[step]
theorem native_first_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (g : Signed62)
    (hn : signed62Normalized g) (hg : signed62Value g = x)
    (hx : 0 ≤ x ∧ x < signed62Value params.helpers.modulus)
    (hgcd : Int.gcd (signed62Value params.helpers.modulus) x = 1) :
    nativeInversionFirst inst params.helpers.modulus g params.r2 ⦃ out =>
      InversionInvariant params x 1 out.f out.g out.d out.e out.eta out.len ⦄ := by
  have hinv := inversion_initial_invariant params x g hn hg hx
  unfold nativeInversionFirst
  apply WP.spec_bind (native_first_fg_spec params x g hinv)
  intro fg hfg
  have hnonzero : active62Value fg.g (5#usize).val ≠ 0 := by
    rw [hfg.g_value]
    exact first_batch_nonzero _ _ params.large params.odd hgcd
  apply WP.spec_bind (inversion_is_zero_spec fg.g 5#usize hinv.length hfg.g_normalized)
  intro zero hzero
  have hz : zero = false := by
    cases zero
    · rfl
    · exact False.elim (hnonzero (hzero.mp rfl))
  simp only [hz, Bool.false_eq_true, not_false_eq_true, massert, ite_true, bind_ok]
  apply WP.spec_bind (native_first_coefficient_spec params x g hinv fg hfg)
  intro de hde
  rcases de with ⟨d, e⟩
  dsimp only at hde ⊢
  rw [fg_result_eq (inversion_fg_range_spec params x 1 fg.f fg.g d e fg.eta 5#usize hde hx)]
  simp only [bind_ok]
  apply WP.spec_bind (shrink_inversion_spec params x 1 fg.f fg.g d e fg.eta 5#usize hde)
  intro result hresult
  rcases result with ⟨f1, g1, len⟩
  simpa only [Std.uncurry_apply_pair, WP.spec_ok] using hresult

#print axioms native_first_spec
end UdonVerify.CommonSigned62
