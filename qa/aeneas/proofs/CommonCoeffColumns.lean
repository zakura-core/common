import CommonCoeffRows

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

structure CoeffColumn where
  accD : I128
  accE : I128
  carryD : I128
  carryE : I128

def CoeffColumnPost (valueD valueE bound : Int) (out : CoeffColumn) : Prop :=
  out.accD.val = valueD ∧ out.accE.val = valueE ∧
  out.carryD.val = out.accD.val / signedRadix ∧ out.carryE.val = out.accE.val / signedRadix ∧
  |out.carryD.val| ≤ bound ∧ |out.carryE.val| ≤ bound

def coeffColumn1 (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (d e m md me : I64) (cd ce : I128) : Result CoeffColumn := do
  let rowD ← fgRowTerm t.u t.v d e
  let addD ← cd + rowD
  let rowE ← fgRowTerm t.q t.r d e
  let addE ← ce + rowE
  let modD ← coeffModTerm m md
  let accD ← addD + modD
  let modE ← coeffModTerm m me
  let accE ← addE + modE
  let carryD ← accD >>> 62#i32
  let carryE ← accE >>> 62#i32
  ok ⟨accD, accE, carryD, carryE⟩

@[step]
theorem coeff_column1_spec (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (d e m md me : I64) (cd ce : I128)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hd : |d.val| ≤ signedRadix) (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hme : |me.val| ≤ 2 * signedRadix)
    (hcd : |cd.val| ≤ 3 * signedRadix + 5) (hce : |ce.val| ≤ 3 * signedRadix + 5) :
    coeffColumn1 t d e m md me cd ce ⦃ out =>
      CoeffColumnPost (cd.val + t.u.val * d.val + t.v.val * e.val + m.val * md.val) (ce.val + t.q.val * d.val + t.r.val * e.val + m.val * me.val) (3 * signedRadix + 5) out ⦄ := by
  unfold coeffColumn1
  step -grind with (fg_row_term_spec t.u t.v d e huv hd he) as ⟨rowD, hrowD, hrowDBound⟩
  step -grind with (coeff_add_row_spec cd rowD hcd hrowDBound) as ⟨addD, haddD, haddDBound⟩
  step -grind with (fg_row_term_spec t.q t.r d e hqr hd he) as ⟨rowE, hrowE, hrowEBound⟩
  step -grind with (coeff_add_row_spec ce rowE hce hrowEBound) as ⟨addE, haddE, haddEBound⟩
  step -grind with (coeff_mod_term_spec m md hm hmd) as ⟨modD, hmodD, hmodDBound⟩
  step -grind with (coeff_add_mod_spec addD modD haddDBound hmodDBound) as ⟨accD, haccD, haccDBound⟩
  step -grind with (coeff_mod_term_spec m me hm hme) as ⟨modE, hmodE, hmodEBound⟩
  step -grind with (coeff_add_mod_spec addE modE haddEBound hmodEBound) as ⟨accE, haccE, haccEBound⟩
  step -grind with (coeff_shift_spec accD haccDBound) as ⟨carryD, hcarryD, hcarryDBound⟩
  step -grind with (coeff_shift_spec accE haccEBound) as ⟨carryE, hcarryE, hcarryEBound⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, hcarryD, hcarryE, hcarryDBound, hcarryEBound⟩
  · rw [haccD, haddD, hrowD, hmodD]
    ring
  · rw [haccE, haddE, hrowE, hmodE]
    ring

#print axioms coeff_column1_spec

def coeffColumn2 (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (d e m md me : I64) (cd ce : I128) : Result CoeffColumn := do
  let rowD ← fgRowTerm t.u t.v d e
  let addD ← cd + rowD
  let rowE ← fgRowTerm t.q t.r d e
  let addE ← ce + rowE
  let modD ← core.convert.num.FromI128I64.from md <<< 1#i32
  let accD ← addD + modD
  let modE ← core.convert.num.FromI128I64.from me <<< 1#i32
  let accE ← addE + modE
  let carryD ← accD >>> 62#i32
  let carryE ← accE >>> 62#i32
  ok ⟨accD, accE, carryD, carryE⟩

@[step]
theorem coeff_column2_spec (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (d e m md me : I64) (cd ce : I128)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hd : |d.val| ≤ signedRadix) (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hme : |me.val| ≤ 2 * signedRadix)
    (hcd : |cd.val| ≤ 3 * signedRadix + 5) (hce : |ce.val| ≤ 3 * signedRadix + 5) :
    coeffColumn2 t d e m md me cd ce ⦃ out =>
      CoeffColumnPost (cd.val + t.u.val * d.val + t.v.val * e.val + 2 * md.val) (ce.val + t.q.val * d.val + t.r.val * e.val + 2 * me.val) (3 * signedRadix + 5) out ⦄ := by
  unfold coeffColumn2
  step -grind with (fg_row_term_spec t.u t.v d e huv hd he) as ⟨rowD, hrowD, hrowDBound⟩
  step -grind with (coeff_add_row_spec cd rowD hcd hrowDBound) as ⟨addD, haddD, haddDBound⟩
  step -grind with (fg_row_term_spec t.q t.r d e hqr hd he) as ⟨rowE, hrowE, hrowEBound⟩
  step -grind with (coeff_add_row_spec ce rowE hce hrowEBound) as ⟨addE, haddE, haddEBound⟩
  step -grind with (fg_widen_shift_spec md 1#i32 (Or.inl rfl)) as ⟨modD, hmodD⟩
  change modD.val = md.val * 2 at hmodD
  have hmodDBound : |modD.val| ≤ 2 * signedRadix ^ 2 := by
    rw [hmodD, abs_mul]
    norm_num
    norm_num only [signedRadix] at hmd ⊢
    omega
  step -grind with (coeff_add_mod_spec addD modD haddDBound hmodDBound) as ⟨accD, haccD, haccDBound⟩
  step -grind with (fg_widen_shift_spec me 1#i32 (Or.inl rfl)) as ⟨modE, hmodE⟩
  change modE.val = me.val * 2 at hmodE
  have hmodEBound : |modE.val| ≤ 2 * signedRadix ^ 2 := by
    rw [hmodE, abs_mul]
    norm_num
    norm_num only [signedRadix] at hme ⊢
    omega
  step -grind with (coeff_add_mod_spec addE modE haddEBound hmodEBound) as ⟨accE, haccE, haccEBound⟩
  step -grind with (coeff_shift_spec accD haccDBound) as ⟨carryD, hcarryD, hcarryDBound⟩
  step -grind with (coeff_shift_spec accE haccEBound) as ⟨carryE, hcarryE, hcarryEBound⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, hcarryD, hcarryE, hcarryDBound, hcarryEBound⟩
  · rw [haccD, haddD, hrowD, hmodD]
    ring
  · rw [haccE, haddE, hrowE, hmodE]
    ring

#print axioms coeff_column2_spec

def coeffColumn3 (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (d e m md me : I64) (cd ce : I128) : Result CoeffColumn := do
  let rowD ← fgRowTerm t.u t.v d e
  let accD ← cd + rowD
  let rowE ← fgRowTerm t.q t.r d e
  let accE ← ce + rowE
  let carryD ← accD >>> 62#i32
  let carryE ← accE >>> 62#i32
  ok ⟨accD, accE, carryD, carryE⟩

@[step]
theorem coeff_column3_spec (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (d e m md me : I64) (cd ce : I128)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hd : |d.val| ≤ signedRadix) (he : |e.val| ≤ signedRadix) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hme : |me.val| ≤ 2 * signedRadix)
    (hcd : |cd.val| ≤ 3 * signedRadix + 5) (hce : |ce.val| ≤ 3 * signedRadix + 5) :
    coeffColumn3 t d e m md me cd ce ⦃ out =>
      CoeffColumnPost (cd.val + t.u.val * d.val + t.v.val * e.val) (ce.val + t.q.val * d.val + t.r.val * e.val) (3 * signedRadix + 5) out ⦄ := by
  unfold coeffColumn3
  step -grind with (fg_row_term_spec t.u t.v d e huv hd he) as ⟨rowD, hrowD, hrowDBound⟩
  step -grind with (coeff_add_row_spec cd rowD hcd hrowDBound) as ⟨accD, haccD, haccDBound⟩
  step -grind with (fg_row_term_spec t.q t.r d e hqr hd he) as ⟨rowE, hrowE, hrowEBound⟩
  step -grind with (coeff_add_row_spec ce rowE hce hrowEBound) as ⟨accE, haccE, haccEBound⟩
  step -grind with (coeff_shift_spec accD (by norm_num only [signedRadix] at haccDBound ⊢; omega)) as ⟨carryD, hcarryD, hcarryDBound⟩
  step -grind with (coeff_shift_spec accE (by norm_num only [signedRadix] at haccEBound ⊢; omega)) as ⟨carryE, hcarryE, hcarryEBound⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, hcarryD, hcarryE, hcarryDBound, hcarryEBound⟩
  · rw [haccD, hrowD]
    ring
  · rw [haccE, hrowE]
    ring

#print axioms coeff_column3_spec

def coeffColumn4 (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (d e m md me : I64) (cd ce : I128) : Result CoeffColumn := do
  let rowD ← fgRowTerm t.u t.v d e
  let addD ← cd + rowD
  let rowE ← fgRowTerm t.q t.r d e
  let addE ← ce + rowE
  let modD ← core.convert.num.FromI128I64.from md <<< 6#i32
  let accD ← addD + modD
  let modE ← core.convert.num.FromI128I64.from me <<< 6#i32
  let accE ← addE + modE
  let carryD ← accD >>> 62#i32
  let carryE ← accE >>> 62#i32
  ok ⟨accD, accE, carryD, carryE⟩

@[step]
theorem coeff_column4_spec (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (d e m md me : I64) (cd ce : I128)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hd : |d.val| ≤ 256) (he : |e.val| ≤ 256) (hm : |m.val| ≤ signedRadix)
    (hmd : |md.val| ≤ 2 * signedRadix) (hme : |me.val| ≤ 2 * signedRadix)
    (hcd : |cd.val| ≤ 3 * signedRadix + 5) (hce : |ce.val| ≤ 3 * signedRadix + 5) :
    coeffColumn4 t d e m md me cd ce ⦃ out =>
      CoeffColumnPost (cd.val + t.u.val * d.val + t.v.val * e.val + 64 * md.val) (ce.val + t.q.val * d.val + t.r.val * e.val + 64 * me.val) (388) out ⦄ := by
  unfold coeffColumn4
  step -grind with (coeff_top_term_spec t.u t.v d e huv hd he) as ⟨rowD, hrowD, hrowDBound⟩
  step -grind with (coeff_top_add_row_spec cd rowD hcd hrowDBound) as ⟨addD, haddD, haddDBound⟩
  step -grind with (coeff_top_term_spec t.q t.r d e hqr hd he) as ⟨rowE, hrowE, hrowEBound⟩
  step -grind with (coeff_top_add_row_spec ce rowE hce hrowEBound) as ⟨addE, haddE, haddEBound⟩
  step -grind with (fg_widen_shift_spec md 6#i32 (Or.inr rfl)) as ⟨modD, hmodD⟩
  change modD.val = md.val * 64 at hmodD
  have hmodDBound : |modD.val| ≤ 128 * signedRadix := by
    rw [hmodD, abs_mul]
    norm_num
    norm_num only [signedRadix] at hmd ⊢
    omega
  step -grind with (coeff_top_add_mod_spec addD modD haddDBound hmodDBound) as ⟨accD, haccD, haccDBound⟩
  step -grind with (fg_widen_shift_spec me 6#i32 (Or.inr rfl)) as ⟨modE, hmodE⟩
  change modE.val = me.val * 64 at hmodE
  have hmodEBound : |modE.val| ≤ 128 * signedRadix := by
    rw [hmodE, abs_mul]
    norm_num
    norm_num only [signedRadix] at hme ⊢
    omega
  step -grind with (coeff_top_add_mod_spec addE modE haddEBound hmodEBound) as ⟨accE, haccE, haccEBound⟩
  step -grind with (coeff_top_shift_spec accD haccDBound) as ⟨carryD, hcarryD, hcarryDBound⟩
  step -grind with (coeff_top_shift_spec accE haccEBound) as ⟨carryE, hcarryE, hcarryEBound⟩
  try simp only [WP.spec_ok]
  refine ⟨?_, ?_, hcarryD, hcarryE, hcarryDBound, hcarryEBound⟩
  · rw [haccD, haddD, hrowD, hmodD]
    ring
  · rw [haccE, haddE, hrowE, hmodE]
    ring

#print axioms coeff_column4_spec

end UdonVerify.CommonSigned62
