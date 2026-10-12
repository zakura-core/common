import CommonCoeffSpecialMath

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def firstCoeffColumn1 (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (e m md me : I64) (cd ce : I128) : Result CoeffColumn := do
  let rowD ← fgZeroTerm t.v e
  let modD ← coeffModTerm m md
  let sumD ← rowD + modD
  let accD ← cd + sumD
  let rowE ← fgZeroTerm t.r e
  let modE ← coeffModTerm m me
  let sumE ← rowE + modE
  let accE ← ce + sumE
  let carryD ← accD >>> 62#i32
  let carryE ← accE >>> 62#i32
  ok ⟨accD, accE, carryD, carryE⟩

@[step]
theorem first_coeff_column1_spec (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (e m md me : I64) (cd ce : I128)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hme : |me.val| ≤ 2 * signedRadix)
    (hcd : |cd.val| ≤ 3 * signedRadix + 5) (hce : |ce.val| ≤ 3 * signedRadix + 5) :
    firstCoeffColumn1 t e m md me cd ce ⦃ out =>
      CoeffColumnPost (cd.val + t.v.val * e.val + m.val * md.val)
        (ce.val + t.r.val * e.val + m.val * me.val) (3 * signedRadix + 5) out ⦄ := by
  have hv : |t.v.val| ≤ signedRadix := by have := abs_nonneg t.u.val; omega
  have hr : |t.r.val| ≤ signedRadix := by have := abs_nonneg t.q.val; omega
  unfold firstCoeffColumn1
  step -grind with (first_product_spec t.v e signedRadix hv he (by norm_num [signedRadix]))
    as ⟨rowD, hrowD, hrowDProductBound⟩
  have hrowDBound : |rowD.val| ≤ signedRadix ^ 2 := by nlinarith only [hrowDProductBound]
  step -grind with (coeff_mod_term_spec m md hm hmd) as ⟨modD, hmodD, hmodDBound⟩
  step -grind with (coeff_bounded_add_spec rowD modD (signedRadix ^ 2) (2 * signedRadix ^ 2)
    hrowDBound hmodDBound (by norm_num [signedRadix])) as ⟨sumD, hsumD, hsumDBound⟩
  step -grind with (coeff_bounded_add_spec cd sumD (3 * signedRadix + 5) (signedRadix ^ 2 + 2 * signedRadix ^ 2)
    hcd hsumDBound (by norm_num [signedRadix])) as ⟨accD, haccD, haccDBound⟩
  step -grind with (first_product_spec t.r e signedRadix hr he (by norm_num [signedRadix]))
    as ⟨rowE, hrowE, hrowEProductBound⟩
  have hrowEBound : |rowE.val| ≤ signedRadix ^ 2 := by nlinarith only [hrowEProductBound]
  step -grind with (coeff_mod_term_spec m me hm hme) as ⟨modE, hmodE, hmodEBound⟩
  step -grind with (coeff_bounded_add_spec rowE modE (signedRadix ^ 2) (2 * signedRadix ^ 2)
    hrowEBound hmodEBound (by norm_num [signedRadix])) as ⟨sumE, hsumE, hsumEBound⟩
  step -grind with (coeff_bounded_add_spec ce sumE (3 * signedRadix + 5) (signedRadix ^ 2 + 2 * signedRadix ^ 2)
    hce hsumEBound (by norm_num [signedRadix])) as ⟨accE, haccE, haccEBound⟩
  step -grind with (coeff_shift_spec accD (by norm_num only [signedRadix] at haccDBound ⊢; omega))
    as ⟨carryD, hcarryD, hcarryDBound⟩
  step -grind with (coeff_shift_spec accE (by norm_num only [signedRadix] at haccEBound ⊢; omega))
    as ⟨carryE, hcarryE, hcarryEBound⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, hcarryD, hcarryE, hcarryDBound, hcarryEBound⟩
  · rw [haccD, hsumD, hrowD, hmodD]
    ring
  · rw [haccE, hsumE, hrowE, hmodE]
    ring

#print axioms first_coeff_column1_spec

def firstCoeffColumn2 (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (e m md me : I64) (cd ce : I128) : Result CoeffColumn := do
  let rowD ← fgZeroTerm t.v e
  let modD ← core.convert.num.FromI128I64.from md <<< 1#i32
  let sumD ← rowD + modD
  let accD ← cd + sumD
  let rowE ← fgZeroTerm t.r e
  let modE ← core.convert.num.FromI128I64.from me <<< 1#i32
  let sumE ← rowE + modE
  let accE ← ce + sumE
  let carryD ← accD >>> 62#i32
  let carryE ← accE >>> 62#i32
  ok ⟨accD, accE, carryD, carryE⟩

@[step]
theorem first_coeff_column2_spec (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (e m md me : I64) (cd ce : I128)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hme : |me.val| ≤ 2 * signedRadix)
    (hcd : |cd.val| ≤ 3 * signedRadix + 5) (hce : |ce.val| ≤ 3 * signedRadix + 5) :
    firstCoeffColumn2 t e m md me cd ce ⦃ out =>
      CoeffColumnPost (cd.val + t.v.val * e.val + 2 * md.val)
        (ce.val + t.r.val * e.val + 2 * me.val) (3 * signedRadix + 5) out ⦄ := by
  have hv : |t.v.val| ≤ signedRadix := by have := abs_nonneg t.u.val; omega
  have hr : |t.r.val| ≤ signedRadix := by have := abs_nonneg t.q.val; omega
  unfold firstCoeffColumn2
  step -grind with (first_product_spec t.v e signedRadix hv he (by norm_num [signedRadix]))
    as ⟨rowD, hrowD, hrowDProductBound⟩
  have hrowDBound : |rowD.val| ≤ signedRadix ^ 2 := by nlinarith only [hrowDProductBound]
  step -grind with (fg_widen_shift_spec md 1#i32 (Or.inl rfl)) as ⟨modD, hmodD⟩
  change modD.val = md.val * 2 at hmodD
  have hmodDBound : |modD.val| ≤ 2 * signedRadix ^ 2 := by
    rw [hmodD, abs_mul]
    norm_num
    norm_num only [signedRadix] at hmd ⊢
    omega
  step -grind with (coeff_bounded_add_spec rowD modD (signedRadix ^ 2) (2 * signedRadix ^ 2)
    hrowDBound hmodDBound (by norm_num [signedRadix])) as ⟨sumD, hsumD, hsumDBound⟩
  step -grind with (coeff_bounded_add_spec cd sumD (3 * signedRadix + 5) (signedRadix ^ 2 + 2 * signedRadix ^ 2)
    hcd hsumDBound (by norm_num [signedRadix])) as ⟨accD, haccD, haccDBound⟩
  step -grind with (first_product_spec t.r e signedRadix hr he (by norm_num [signedRadix]))
    as ⟨rowE, hrowE, hrowEProductBound⟩
  have hrowEBound : |rowE.val| ≤ signedRadix ^ 2 := by nlinarith only [hrowEProductBound]
  step -grind with (fg_widen_shift_spec me 1#i32 (Or.inl rfl)) as ⟨modE, hmodE⟩
  change modE.val = me.val * 2 at hmodE
  have hmodEBound : |modE.val| ≤ 2 * signedRadix ^ 2 := by
    rw [hmodE, abs_mul]
    norm_num
    norm_num only [signedRadix] at hme ⊢
    omega
  step -grind with (coeff_bounded_add_spec rowE modE (signedRadix ^ 2) (2 * signedRadix ^ 2)
    hrowEBound hmodEBound (by norm_num [signedRadix])) as ⟨sumE, hsumE, hsumEBound⟩
  step -grind with (coeff_bounded_add_spec ce sumE (3 * signedRadix + 5) (signedRadix ^ 2 + 2 * signedRadix ^ 2)
    hce hsumEBound (by norm_num [signedRadix])) as ⟨accE, haccE, haccEBound⟩
  step -grind with (coeff_shift_spec accD (by norm_num only [signedRadix] at haccDBound ⊢; omega))
    as ⟨carryD, hcarryD, hcarryDBound⟩
  step -grind with (coeff_shift_spec accE (by norm_num only [signedRadix] at haccEBound ⊢; omega))
    as ⟨carryE, hcarryE, hcarryEBound⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, hcarryD, hcarryE, hcarryDBound, hcarryEBound⟩
  · rw [haccD, hsumD, hrowD, hmodD]
    ring
  · rw [haccE, hsumE, hrowE, hmodE]
    ring

#print axioms first_coeff_column2_spec

def firstCoeffColumn3 (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (e m md me : I64) (cd ce : I128) : Result CoeffColumn := do
  let rowD ← fgZeroTerm t.v e
  let accD ← cd + rowD
  let rowE ← fgZeroTerm t.r e
  let accE ← ce + rowE
  let carryD ← accD >>> 62#i32
  let carryE ← accE >>> 62#i32
  ok ⟨accD, accE, carryD, carryE⟩

@[step]
theorem first_coeff_column3_spec (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (e m md me : I64) (cd ce : I128)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hme : |me.val| ≤ 2 * signedRadix)
    (hcd : |cd.val| ≤ 3 * signedRadix + 5) (hce : |ce.val| ≤ 3 * signedRadix + 5) :
    firstCoeffColumn3 t e m md me cd ce ⦃ out =>
      CoeffColumnPost (cd.val + t.v.val * e.val)
        (ce.val + t.r.val * e.val) (3 * signedRadix + 5) out ⦄ := by
  have hv : |t.v.val| ≤ signedRadix := by have := abs_nonneg t.u.val; omega
  have hr : |t.r.val| ≤ signedRadix := by have := abs_nonneg t.q.val; omega
  unfold firstCoeffColumn3
  step -grind with (first_product_spec t.v e signedRadix hv he (by norm_num [signedRadix]))
    as ⟨rowD, hrowD, hrowDProductBound⟩
  have hrowDBound : |rowD.val| ≤ signedRadix ^ 2 := by nlinarith only [hrowDProductBound]
  step -grind with (coeff_add_row_spec cd rowD hcd hrowDBound) as ⟨accD, haccD, haccDBound⟩
  step -grind with (first_product_spec t.r e signedRadix hr he (by norm_num [signedRadix]))
    as ⟨rowE, hrowE, hrowEProductBound⟩
  have hrowEBound : |rowE.val| ≤ signedRadix ^ 2 := by nlinarith only [hrowEProductBound]
  step -grind with (coeff_add_row_spec ce rowE hce hrowEBound) as ⟨accE, haccE, haccEBound⟩
  step -grind with (coeff_shift_spec accD (by norm_num only [signedRadix] at haccDBound ⊢; omega))
    as ⟨carryD, hcarryD, hcarryDBound⟩
  step -grind with (coeff_shift_spec accE (by norm_num only [signedRadix] at haccEBound ⊢; omega))
    as ⟨carryE, hcarryE, hcarryEBound⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, hcarryD, hcarryE, hcarryDBound, hcarryEBound⟩
  · rw [haccD, hrowD]
  · rw [haccE, hrowE]

#print axioms first_coeff_column3_spec

def firstCoeffColumn4 (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (e m md me : I64) (cd ce : I128) : Result CoeffColumn := do
  let rowD ← fgZeroTerm t.v e
  let modD ← core.convert.num.FromI128I64.from md <<< 6#i32
  let sumD ← rowD + modD
  let accD ← cd + sumD
  let rowE ← fgZeroTerm t.r e
  let modE ← core.convert.num.FromI128I64.from me <<< 6#i32
  let sumE ← rowE + modE
  let accE ← ce + sumE
  let carryD ← accD >>> 62#i32
  let carryE ← accE >>> 62#i32
  ok ⟨accD, accE, carryD, carryE⟩

@[step]
theorem first_coeff_column4_spec (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (e m md me : I64) (cd ce : I128)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (he : |e.val| ≤ 256) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hme : |me.val| ≤ 2 * signedRadix)
    (hcd : |cd.val| ≤ 3 * signedRadix + 5) (hce : |ce.val| ≤ 3 * signedRadix + 5) :
    firstCoeffColumn4 t e m md me cd ce ⦃ out =>
      CoeffColumnPost (cd.val + t.v.val * e.val + 64 * md.val)
        (ce.val + t.r.val * e.val + 64 * me.val) (388) out ⦄ := by
  have hv : |t.v.val| ≤ signedRadix := by have := abs_nonneg t.u.val; omega
  have hr : |t.r.val| ≤ signedRadix := by have := abs_nonneg t.q.val; omega
  unfold firstCoeffColumn4
  step -grind with (first_product_spec t.v e 256 hv he (by norm_num [signedRadix]))
    as ⟨rowD, hrowD, hrowDProductBound⟩
  have hrowDBound : |rowD.val| ≤ 256 * signedRadix := by nlinarith only [hrowDProductBound]
  step -grind with (fg_widen_shift_spec md 6#i32 (Or.inr rfl)) as ⟨modD, hmodD⟩
  change modD.val = md.val * 64 at hmodD
  have hmodDBound : |modD.val| ≤ 128 * signedRadix := by
    rw [hmodD, abs_mul]
    norm_num
    norm_num only [signedRadix] at hmd ⊢
    omega
  step -grind with (coeff_bounded_add_spec rowD modD (256 * signedRadix) (128 * signedRadix)
    hrowDBound hmodDBound (by norm_num [signedRadix])) as ⟨sumD, hsumD, hsumDBound⟩
  step -grind with (coeff_bounded_add_spec cd sumD (3 * signedRadix + 5) (256 * signedRadix + 128 * signedRadix)
    hcd hsumDBound (by norm_num [signedRadix])) as ⟨accD, haccD, haccDBound⟩
  step -grind with (first_product_spec t.r e 256 hr he (by norm_num [signedRadix]))
    as ⟨rowE, hrowE, hrowEProductBound⟩
  have hrowEBound : |rowE.val| ≤ 256 * signedRadix := by nlinarith only [hrowEProductBound]
  step -grind with (fg_widen_shift_spec me 6#i32 (Or.inr rfl)) as ⟨modE, hmodE⟩
  change modE.val = me.val * 64 at hmodE
  have hmodEBound : |modE.val| ≤ 128 * signedRadix := by
    rw [hmodE, abs_mul]
    norm_num
    norm_num only [signedRadix] at hme ⊢
    omega
  step -grind with (coeff_bounded_add_spec rowE modE (256 * signedRadix) (128 * signedRadix)
    hrowEBound hmodEBound (by norm_num [signedRadix])) as ⟨sumE, hsumE, hsumEBound⟩
  step -grind with (coeff_bounded_add_spec ce sumE (3 * signedRadix + 5) (256 * signedRadix + 128 * signedRadix)
    hce hsumEBound (by norm_num [signedRadix])) as ⟨accE, haccE, haccEBound⟩
  step -grind with (coeff_top_shift_spec accD (by norm_num only [signedRadix] at haccDBound ⊢; omega))
    as ⟨carryD, hcarryD, hcarryDBound⟩
  step -grind with (coeff_top_shift_spec accE (by norm_num only [signedRadix] at haccEBound ⊢; omega))
    as ⟨carryE, hcarryE, hcarryEBound⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, hcarryD, hcarryE, hcarryDBound, hcarryEBound⟩
  · rw [haccD, hsumD, hrowD, hmodD]
    ring
  · rw [haccE, hsumE, hrowE, hmodE]
    ring

#print axioms first_coeff_column4_spec

end UdonVerify.CommonSigned62
