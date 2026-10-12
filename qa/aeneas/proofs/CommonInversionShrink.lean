import CommonInversionInvariant
import CommonInversionShrinkBounds

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem shrink_inversion_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (f g d e : Signed62)
    (eta : I64) (len : Usize) (hinv : InversionInvariant params x batches f g d e eta len) :
    CommonInversion.field.pasta.safegcd.shrink_len f g len ⦃ out =>
      InversionInvariant params x batches out.1 out.2.1 d e eta out.2.2 ⦄ := by
  classical
  rw [inversion_shrink_bridge]
  apply WP.spec_mono (result_post_and
    (shrink_len_spec f g len hinv.length hinv.f_normalized hinv.g_normalized
      (by intro k _; exact hinv.f_digits k) (by intro k _; exact hinv.g_digits k))
    (shrink_len_all_bounds_spec f g len hinv.length hinv.f_normalized hinv.g_normalized hinv.f_digits hinv.g_digits))
  intro out hout
  rcases hout with ⟨hsmall, hfAll, hgAll⟩
  rcases hsmall with ⟨hnewLen, hlenCases, hfValue, hgValue, hfNormal, hgNormal, hfBound, hgBound, hcanLen, hnotLen⟩
  have hcapacity : |active62Value out.1 out.2.2.val| ≤ signedRadix ^ out.2.2.val ∧
      |active62Value out.2.1 out.2.2.val| ≤ signedRadix ^ out.2.2.val := by
    rcases hlenCases with hequal | hshrunk
    · rw [hfValue, hgValue, hequal]
      exact ⟨hinv.f_capacity, hinv.g_capacity⟩
    · have hcan : CanShrink62 len.val f[len.val - 1]! g[len.val - 1]! := by
        by_contra hnot
        have := hnotLen hnot
        omega
      have hnew : out.2.2.val = len.val - 1 := by omega
      rw [hfValue, hgValue, hnew]
      exact ⟨active62_normalized_value_bound f len.val hinv.length hinv.f_normalized hcan.2.1,
        active62_normalized_value_bound g len.val hinv.length hinv.g_normalized hcan.2.2⟩
  exact {
    length := ⟨hnewLen.1, by have := hinv.length.2; omega⟩
    f_value := hfValue.trans hinv.f_value
    g_value := hgValue.trans hinv.g_value
    eta_value := hinv.eta_value
    f_normalized := hfNormal
    g_normalized := hgNormal
    f_digits := hfAll
    g_digits := hgAll
    f_capacity := hcapacity.1
    g_capacity := hcapacity.2
    d_normalized := hinv.d_normalized
    e_normalized := hinv.e_normalized
    d_range := hinv.d_range
    e_range := hinv.e_range
    d_bezout := by simpa only [hfValue] using hinv.d_bezout
    e_bezout := by simpa only [hgValue] using hinv.e_bezout }

#print axioms shrink_inversion_spec
end UdonVerify.CommonSigned62
