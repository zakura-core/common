import CommonInvParameters

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem active62_modulus_top_bound {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (a : Signed62) (len : Usize)
    (hn : active62Normalized a len.val)
    (hr : -signed62Value params.modulus < active62Value a len.val ∧
      active62Value a len.val ≤ signed62Value params.modulus) :
    len.val = 5 → |a[4]!.val| ≤ 256 := by
  intro hlen
  have han : signed62Normalized a := by
    intro k
    exact hn ⟨k.val, by omega⟩ (by rw [hlen]; have := k.isLt; dsimp; omega)
  rw [hlen, active62_value_five] at hr
  have hp := params.positive
  have hb := params.bound
  exact (signed62_small_value_bounds a han (by norm_num only at hb ⊢; constructor <;> omega)).2

@[step]
theorem assert_fg_range_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (f g : Signed62) (len : Usize)
    (hlen : 1 ≤ len.val ∧ len.val ≤ 5)
    (hnf : active62Normalized f len.val) (hng : active62Normalized g len.val)
    (hf : ∀ k : Fin 5, |f[k.val]!.val| ≤ signedRadix)
    (hg : ∀ k : Fin 5, |g[k.val]!.val| ≤ signedRadix)
    (hfr : -signed62Value params.modulus < active62Value f len.val ∧
      active62Value f len.val ≤ signed62Value params.modulus)
    (hgr : -signed62Value params.modulus < active62Value g len.val ∧
      active62Value g len.val < signed62Value params.modulus) :
    CommonInvHelpers.field.pasta.safegcd.checks.assert_fg_range inst f g len ⦃ out => out = () ⦄ := by
  obtain ⟨hm, hmt⟩ := inv_modulus_digit_bounds inst params
  have hft := active62_modulus_top_bound params f len hnf hfr
  have hgt := active62_modulus_top_bound params g len hng ⟨hgr.1, _root_.le_of_lt hgr.2⟩
  unfold CommonInvHelpers.field.pasta.safegcd.checks.assert_fg_range
  rw [params.modulus_eq]
  simp only [bind_ok]
  apply WP.spec_bind (check_mul_cmp_62_spec f len params.modulus (-1)#i64 hlen.2 (by decide)
    hf hm hft hmt)
  intro first hfirst
  have hfirstCompare : IntegerCompareResult (active62Value f len.val) (-signed62Value params.modulus) first := by
    simpa only [show ((-1)#i64).val = -1 from by decide, neg_one_mul] using hfirst
  have hfirstGt : first = .gt := (integer_compare_tags _ _ first hfirstCompare).2.2.mpr hfr.1
  simp only [hfirstGt, CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, bind_ok]
  simp [massert]
  apply WP.spec_bind (check_mul_cmp_62_spec f len params.modulus 1#i64 hlen.2 (by decide) hf hm hft hmt)
  intro second hsecond
  have hsecondCompare : IntegerCompareResult (active62Value f len.val) (signed62Value params.modulus) second := by
    simpa only [show (1#i64).val = 1 from by decide, one_mul] using hsecond
  have hsecondNotGt : second ≠ .gt := by
    intro hgt
    have := (integer_compare_tags _ _ second hsecondCompare).2.2.mp hgt
    omega
  have hsecondCall : core.cmp.PartialEq.ne.trait_default
      CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering second Ordering.gt = ok true := by
    cases second <;> simp_all [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, Bind.bind]
  rw [hsecondCall]
  simp [massert]
  apply WP.spec_bind (check_mul_cmp_62_spec g len params.modulus (-1)#i64 hlen.2 (by decide) hg hm hgt hmt)
  intro third hthird
  have hthirdCompare : IntegerCompareResult (active62Value g len.val) (-signed62Value params.modulus) third := by
    simpa only [show ((-1)#i64).val = -1 from by decide, neg_one_mul] using hthird
  have hthirdGt : third = .gt := (integer_compare_tags _ _ third hthirdCompare).2.2.mpr hgr.1
  simp only [hthirdGt, CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, bind_ok]
  simp [massert]
  apply WP.spec_bind (check_mul_cmp_62_spec g len params.modulus 1#i64 hlen.2 (by decide) hg hm hgt hmt)
  intro fourth hfourth
  have hfourthCompare : IntegerCompareResult (active62Value g len.val) (signed62Value params.modulus) fourth := by
    simpa only [show (1#i64).val = 1 from by decide, one_mul] using hfourth
  have hfourthLt : fourth = .lt := (integer_compare_tags _ _ fourth hfourthCompare).1.mpr hgr.2
  simp [hfourthLt, CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, massert, WP.spec_ok]

#print axioms active62_modulus_top_bound
#print axioms assert_fg_range_spec
end UdonVerify.CommonSigned62
