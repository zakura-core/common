import CommonShrinkCompose
import CommonShrinkMath

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def Shrink62Result (f g : Signed62) (len : Usize) (out : Signed62 × Signed62 × Usize) : Prop :=
  (1 ≤ out.2.2.val ∧ out.2.2.val ≤ len.val) ∧
  (out.2.2.val = len.val ∨ out.2.2.val + 1 = len.val) ∧
  active62Value out.1 out.2.2.val = active62Value f len.val ∧
  active62Value out.2.1 out.2.2.val = active62Value g len.val ∧
  active62Normalized out.1 out.2.2.val ∧ active62Normalized out.2.1 out.2.2.val ∧
  fgInputsBounded out.2.2.val out.1 ∧ fgInputsBounded out.2.2.val out.2.1 ∧
  (CanShrink62 len.val f[len.val - 1]! g[len.val - 1]! → out.2.2.val = len.val - 1) ∧
  (¬CanShrink62 len.val f[len.val - 1]! g[len.val - 1]! → out.2.2.val = len.val)

@[step]
theorem shrink_len_spec (f g : Signed62) (len : Usize) (hlen : 1 ≤ len.val ∧ len.val ≤ 5)
    (hnf : active62Normalized f len.val) (hng : active62Normalized g len.val)
    (hbf : fgInputsBounded len.val f) (hbg : fgInputsBounded len.val g) :
    CommonInvHelpers.field.pasta.safegcd.shrink_len f g len ⦃ out => Shrink62Result f g len out ⦄ := by
  classical
  rw [shrink_columns_bridge]
  unfold shrinkColumns
  step +scalarTac -grind with Usize.sub_spec as ⟨topIndex, htop⟩
  have htopBound : topIndex.val < 5 := by omega
  rw [fg_index_eq f topIndex htopBound, fg_index_eq g topIndex htopBound]
  simp only [bind_ok]
  apply WP.spec_bind (shrink_length_mask_spec len hlen)
  intro lengthMask hmask
  subst lengthMask
  rw [coeff_sign_shift_eq, coeff_sign_shift_eq]
  simp only [bind_ok]
  by_cases hcan : CanShrink62 len.val f[topIndex.val]! g[topIndex.val]!
  · rw [if_pos ((shrink_condition_iff _ _ _).mpr hcan)]
    obtain ⟨hlarge, hfTop, hgTop⟩ := hcan
    step +scalarTac -grind with Usize.sub_spec as ⟨lowIndex, hlow⟩
    have hlowBound : lowIndex.val < 5 := by omega
    rw [fg_index_eq f lowIndex hlowBound]
    simp only [bind_ok]
    have hfLow : 0 ≤ f[lowIndex.val]!.val ∧ f[lowIndex.val]!.val < signedRadix :=
      hnf ⟨lowIndex.val, hlowBound⟩ (by dsimp; omega)
    apply WP.spec_bind (shrink_digit_spec f[lowIndex.val]! f[topIndex.val]! hfLow hfTop)
    intro fDigit hfDigit
    rw [fg_update_eq f lowIndex fDigit hlowBound, fg_index_eq g lowIndex hlowBound]
    simp only [bind_ok]
    have hgLow : 0 ≤ g[lowIndex.val]!.val ∧ g[lowIndex.val]!.val < signedRadix :=
      hng ⟨lowIndex.val, hlowBound⟩ (by dsimp; omega)
    apply WP.spec_bind (shrink_digit_spec g[lowIndex.val]! g[topIndex.val]! hgLow hgTop)
    intro gDigit hgDigit
    rw [fg_update_eq g lowIndex gDigit hlowBound]
    simp only [bind_ok, WP.spec_ok]
    have hfValue : fDigit.val = f[lowIndex.val]!.val + signedRadix * f[len.val - 1]!.val := by
      simpa only [htop] using hfDigit.1
    have hgValue : gDigit.val = g[lowIndex.val]!.val + signedRadix * g[len.val - 1]!.val := by
      simpa only [htop] using hgDigit.1
    have hfFold := active62_fold_value f len.val lowIndex fDigit ⟨hlarge, hlen.2⟩ hlow hfValue
    have hgFold := active62_fold_value g len.val lowIndex gDigit ⟨hlarge, hlen.2⟩ hlow hgValue
    have hfNorm := active62_fold_normalized f len.val lowIndex fDigit ⟨hlarge, hlen.2⟩ hlow hnf
    have hgNorm := active62_fold_normalized g len.val lowIndex gDigit ⟨hlarge, hlen.2⟩ hlow hng
    have hfBound := active62_fold_bounded f len.val lowIndex fDigit ⟨hlarge, hlen.2⟩ hlow hbf hfDigit.2
    have hgBound := active62_fold_bounded g len.val lowIndex gDigit ⟨hlarge, hlen.2⟩ hlow hbg hgDigit.2
    have hcanOriginal : CanShrink62 len.val f[len.val - 1]! g[len.val - 1]! := by
      exact ⟨hlarge, by simpa only [htop] using hfTop, by simpa only [htop] using hgTop⟩
    unfold Shrink62Result
    simp only [htop]
    exact ⟨⟨by omega, by omega⟩, Or.inr (by omega), hfFold, hgFold, hfNorm, hgNorm,
      hfBound, hgBound, by simp, by intro hn; exact (hn hcanOriginal).elim⟩
  · rw [if_neg (by intro hc; exact hcan ((shrink_condition_iff _ _ _).mp hc))]
    simp only [WP.spec_ok]
    have hnotOriginal : ¬CanShrink62 len.val f[len.val - 1]! g[len.val - 1]! := by
      simpa only [htop] using hcan
    exact ⟨⟨hlen.1, _root_.le_refl _⟩, Or.inl rfl, rfl, rfl, hnf, hng, hbf, hbg,
      by intro hc; exact (hnotOriginal hc).elim, by intro _; rfl⟩

#print axioms shrink_len_spec
end UdonVerify.CommonSigned62
