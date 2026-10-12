import CommonFG62FirstRows

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem signed62_eq_of_digits (lhs rhs : Signed62)
    (hdigits : ∀ k : Fin 5, lhs[k.val]!.val = rhs[k.val]!.val) : lhs = rhs := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp only [lhs.property, rhs.property]
  · intro k hk hk'
    have hbound : k < 5 := by simpa [lhs.property] using hk
    have h := IScalar.eq_of_val_eq (hdigits ⟨k, hbound⟩)
    simpa only [Array.getElem!_Nat_eq, getElem!_pos lhs.val k hk,
      getElem!_pos rhs.val k hk'] using h

theorem fg_result_unique {α : Type} {post : α → Prop} (left right : Result α)
    (hl : left ⦃ out => post out ⦄) (hr : right ⦃ out => post out ⦄)
    (hunique : ∀ x y, post x → post y → x = y) : left = right := by
  cases hl
  cases hr
  congr 1
  apply hunique <;> assumption

@[step]
theorem update_fg_62_first_matches_spec {P : Type}
    (inst : CommonFG62First.field.pasta.safegcd.InvParams P) (f g : Signed62)
    (t : CommonFG62First.field.pasta.safegcd.Trans2x2)
    (hparam : inst.MODULUS_62 = ok f)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix)
    (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hshape : f[2]!.val = 2 ∧ f[3]!.val = 0 ∧ f[4]!.val = 64)
    (hf : fgInputsBounded 5 f) (hg : fgInputsBounded 5 g)
    (hdivf : fgRowInteger t.u.val t.v.val f g 0 % signedRadix = 0)
    (hdivg : fgRowInteger t.q.val t.r.val f g 0 % signedRadix = 0) :
    CommonFG62First.field.pasta.safegcd.update_fg_62_first inst f g t ⦃ out =>
      fgRowMatches 5 t.u.val t.v.val f g f out.1 ∧
      fgRowMatches 5 t.q.val t.r.val f g g out.2 ⦄ := by
  rw [fg_first_flat_bridge inst f g t hparam]
  exact fg_first_flat_spec f g t huv hqr hshape hf hg hdivf hdivg

theorem update_fg_62_first_eq_generic {P : Type}
    (inst : CommonFG62First.field.pasta.safegcd.InvParams P) (f g : Signed62)
    (t : CommonFG62First.field.pasta.safegcd.Trans2x2)
    (hparam : inst.MODULUS_62 = ok f)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix)
    (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hshape : f[2]!.val = 2 ∧ f[3]!.val = 0 ∧ f[4]!.val = 64)
    (hf : fgInputsBounded 5 f) (hg : fgInputsBounded 5 g)
    (hdivf : fgRowInteger t.u.val t.v.val f g 0 % signedRadix = 0)
    (hdivg : fgRowInteger t.q.val t.r.val f g 0 % signedRadix = 0) :
    CommonFG62First.field.pasta.safegcd.update_fg_62_first inst f g t =
      CommonFG62.field.pasta.safegcd.update_fg_62_var 5#usize f g
        ⟨t.u, t.v, t.q, t.r⟩ := by
  refine fg_result_unique _ _
    (update_fg_62_first_matches_spec inst f g t hparam huv hqr hshape hf hg hdivf hdivg)
    (fg_all_matches_spec 5#usize f g ⟨t.u, t.v, t.q, t.r⟩
      (by decide) huv hqr hf hg hdivf hdivg) ?_
  intro left right hl hr
  apply Prod.ext
  · apply signed62_eq_of_digits
    intro k
    exact (hl.1 k).trans (hr.1 k).symm
  · apply signed62_eq_of_digits
    intro k
    exact (hl.2 k).trans (hr.2 k).symm

@[step]
theorem update_fg_62_first_spec {P : Type}
    (inst : CommonFG62First.field.pasta.safegcd.InvParams P) (f g : Signed62)
    (t : CommonFG62First.field.pasta.safegcd.Trans2x2)
    (hparam : inst.MODULUS_62 = ok f)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix)
    (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hshape : f[2]!.val = 2 ∧ f[3]!.val = 0 ∧ f[4]!.val = 64)
    (hf : fgInputsBounded 5 f) (hg : fgInputsBounded 5 g)
    (hdivf : fgRowInteger t.u.val t.v.val f g 0 % signedRadix = 0)
    (hdivg : fgRowInteger t.q.val t.r.val f g 0 % signedRadix = 0) :
    CommonFG62First.field.pasta.safegcd.update_fg_62_first inst f g t ⦃ out =>
      signedRadix * signed62Value out.1 =
        t.u.val * signed62Value f + t.v.val * signed62Value g ∧
      signedRadix * signed62Value out.2 =
        t.q.val * signed62Value f + t.r.val * signed62Value g ∧
      signed62Normalized out.1 ∧ signed62Normalized out.2 ⦄ := by
  step -grind with
    (update_fg_62_first_matches_spec inst f g t hparam huv hqr hshape hf hg hdivf hdivg)
    as ⟨out, hfout, hgout⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [active62_value_five] using
      fg_matches_value 5 _ _ _ _ _ _ (by decide) hdivf hfout
  · simpa only [active62_value_five] using
      fg_matches_value 5 _ _ _ _ _ _ (by decide) hdivg hgout
  · intro k
    have hk : k.val < 4 := k.isLt
    have hk5 : k.val < 5 := by omega
    exact fg_matches_normalized 5 _ _ _ _ _ _ hfout ⟨k.val, hk5⟩ (by dsimp; omega)
  · intro k
    have hk : k.val < 4 := k.isLt
    have hk5 : k.val < 5 := by omega
    exact fg_matches_normalized 5 _ _ _ _ _ _ hgout ⟨k.val, hk5⟩ (by dsimp; omega)

#print axioms signed62_eq_of_digits
#print axioms fg_result_unique
#print axioms update_fg_62_first_matches_spec
#print axioms update_fg_62_first_eq_generic
#print axioms update_fg_62_first_spec
end UdonVerify.CommonSigned62
