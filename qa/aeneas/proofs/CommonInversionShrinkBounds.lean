import CommonShrink

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem signed62_set_all_bounds (a : Signed62) (index : Usize) (digit : I64)
    (ha : ∀ k : Fin 5, |a[k.val]!.val| ≤ signedRadix) (hd : |digit.val| ≤ signedRadix) :
    ∀ k : Fin 5, |(a.set index digit)[k.val]!.val| ≤ signedRadix := by
  intro k
  by_cases heq : index.val = k.val
  · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨heq, by simpa using k.isLt⟩]
    exact hd
  · rw [Array.getElem!_Nat_set_ne _ _ _ _ heq]
    exact ha k

theorem result_post_and {α : Type} {result : Result α} {left right : α → Prop}
    (hl : result ⦃ out => left out ⦄) (hr : result ⦃ out => right out ⦄) :
    result ⦃ out => left out ∧ right out ⦄ := by
  obtain ⟨out, hout, hleft⟩ := WP.spec_imp_exists hl
  rw [hout] at hr ⊢
  simp only [WP.spec_ok] at hr ⊢
  exact ⟨hleft, hr⟩

@[step]
theorem shrink_len_all_bounds_spec (f g : Signed62) (len : Usize)
    (hlen : 1 ≤ len.val ∧ len.val ≤ 5)
    (hnf : active62Normalized f len.val) (hng : active62Normalized g len.val)
    (hbf : ∀ k : Fin 5, |f[k.val]!.val| ≤ signedRadix)
    (hbg : ∀ k : Fin 5, |g[k.val]!.val| ≤ signedRadix) :
    CommonInvHelpers.field.pasta.safegcd.shrink_len f g len ⦃ out =>
      (∀ k : Fin 5, |out.1[k.val]!.val| ≤ signedRadix) ∧
      (∀ k : Fin 5, |out.2.1[k.val]!.val| ≤ signedRadix) ⦄ := by
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
    apply WP.spec_bind (shrink_digit_spec f[lowIndex.val]! f[topIndex.val]!
      (hnf ⟨lowIndex.val, hlowBound⟩ (by dsimp; omega)) hfTop)
    intro fDigit hfDigit
    rw [fg_update_eq f lowIndex fDigit hlowBound, fg_index_eq g lowIndex hlowBound]
    simp only [bind_ok]
    apply WP.spec_bind (shrink_digit_spec g[lowIndex.val]! g[topIndex.val]!
      (hng ⟨lowIndex.val, hlowBound⟩ (by dsimp; omega)) hgTop)
    intro gDigit hgDigit
    rw [fg_update_eq g lowIndex gDigit hlowBound]
    simp only [bind_ok, WP.spec_ok]
    exact ⟨signed62_set_all_bounds _ _ _ hbf hfDigit.2, signed62_set_all_bounds _ _ _ hbg hgDigit.2⟩
  · rw [if_neg (by intro hc; exact hcan ((shrink_condition_iff _ _ _).mp hc))]
    simp only [WP.spec_ok]
    exact ⟨hbf, hbg⟩

#print axioms signed62_set_all_bounds
#print axioms result_post_and
#print axioms shrink_len_all_bounds_spec
end UdonVerify.CommonSigned62
