import CommonFG62Case2
import CommonFG62Case3
import CommonFG62Case4
import CommonFG62Case5

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem fg_one_matches_spec (f g : Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix)
    (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hf : fgInputsBounded 1 f) (hg : fgInputsBounded 1 g)
    (hdivf : fgRowInteger t.u.val t.v.val f g 0 % signedRadix = 0)
    (hdivg : fgRowInteger t.q.val t.r.val f g 0 % signedRadix = 0) :
    CommonFG62.field.pasta.safegcd.update_fg_62_var 1#usize f g t ⦃ out =>
      fgRowMatches 1 t.u.val t.v.val f g f out.1 ∧
      fgRowMatches 1 t.q.val t.r.val f g g out.2 ⦄ := by
  step -grind with (fg_one_spec 1#usize f g t (by decide) huv hqr
    (hf ⟨0, by decide⟩ (by decide)) (hg ⟨0, by decide⟩ (by decide)) hdivf hdivg)
    as ⟨out, hvaluef, hvalueg, hinactive⟩
  constructor
  · intro k
    by_cases hk : k.val = 0
    · have heq : k = ⟨0, by decide⟩ := Fin.ext hk
      subst k
      simpa [fgStoredDigit, fgCarry, fgRowInteger] using hvaluef
    · have h := congrArg IScalar.val (hinactive k (by omega)).1
      simpa only [if_neg (show ¬k.val < 1 by omega)] using h
  · intro k
    by_cases hk : k.val = 0
    · have heq : k = ⟨0, by decide⟩ := Fin.ext hk
      subst k
      simpa [fgStoredDigit, fgCarry, fgRowInteger] using hvalueg
    · have h := congrArg IScalar.val (hinactive k (by omega)).2
      simpa only [if_neg (show ¬k.val < 1 by omega)] using h

@[step]
theorem fg_all_matches_spec (len : Usize) (f g : Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2)
    (hlen : 1 ≤ len.val ∧ len.val ≤ 5)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix)
    (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hf : fgInputsBounded len.val f) (hg : fgInputsBounded len.val g)
    (hdivf : fgRowInteger t.u.val t.v.val f g 0 % signedRadix = 0)
    (hdivg : fgRowInteger t.q.val t.r.val f g 0 % signedRadix = 0) :
    CommonFG62.field.pasta.safegcd.update_fg_62_var len f g t ⦃ out =>
      fgRowMatches len.val t.u.val t.v.val f g f out.1 ∧
      fgRowMatches len.val t.q.val t.r.val f g g out.2 ⦄ := by
  have hcases : len.val = 1 ∨ len.val = 2 ∨ len.val = 3 ∨ len.val = 4 ∨ len.val = 5 := by omega
  rcases hcases with h | h | h | h | h
  · have heq : len = 1#usize := UScalar.eq_of_val_eq h
    subst len
    exact fg_one_matches_spec f g t huv hqr hf hg hdivf hdivg
  · have heq : len = 2#usize := UScalar.eq_of_val_eq h
    subst len
    rw [fg_flat_2_bridge]
    exact fg_flat_2_spec f g t huv hqr hf hg hdivf hdivg
  · have heq : len = 3#usize := UScalar.eq_of_val_eq h
    subst len
    rw [fg_flat_3_bridge]
    exact fg_flat_3_spec f g t huv hqr hf hg hdivf hdivg
  · have heq : len = 4#usize := UScalar.eq_of_val_eq h
    subst len
    rw [fg_flat_4_bridge]
    exact fg_flat_4_spec f g t huv hqr hf hg hdivf hdivg
  · have heq : len = 5#usize := UScalar.eq_of_val_eq h
    subst len
    rw [fg_flat_5_bridge]
    exact fg_flat_5_spec f g t huv hqr hf hg hdivf hdivg

@[step]
theorem update_fg_62_var_spec (len : Usize) (f g : Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2)
    (hlen : 1 ≤ len.val ∧ len.val ≤ 5)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix)
    (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hf : fgInputsBounded len.val f) (hg : fgInputsBounded len.val g)
    (hdivf : fgRowInteger t.u.val t.v.val f g 0 % signedRadix = 0)
    (hdivg : fgRowInteger t.q.val t.r.val f g 0 % signedRadix = 0) :
    CommonFG62.field.pasta.safegcd.update_fg_62_var len f g t ⦃ out =>
      signedRadix * active62Value out.1 len.val =
        t.u.val * active62Value f len.val + t.v.val * active62Value g len.val ∧
      signedRadix * active62Value out.2 len.val =
        t.q.val * active62Value f len.val + t.r.val * active62Value g len.val ∧
      (∀ k : Fin 5, k.val + 1 < len.val →
        (0 ≤ out.1[k.val]!.val ∧ out.1[k.val]!.val < signedRadix) ∧
        (0 ≤ out.2[k.val]!.val ∧ out.2[k.val]!.val < signedRadix)) ∧
      (∀ k : Fin 5, len.val ≤ k.val →
        out.1[k.val]! = f[k.val]! ∧ out.2[k.val]! = g[k.val]!) ⦄ := by
  step -grind with (fg_all_matches_spec len f g t hlen huv hqr hf hg hdivf hdivg)
    as ⟨out, hfout, hgout⟩
  refine ⟨fg_matches_value _ _ _ _ _ _ _ hlen hdivf hfout,
    fg_matches_value _ _ _ _ _ _ _ hlen hdivg hgout, ?_, ?_⟩
  · intro k hk
    simpa only [and_assoc] using
      And.intro (fg_matches_normalized _ _ _ _ _ _ _ hfout k hk)
        (fg_matches_normalized _ _ _ _ _ _ _ hgout k hk)
  · intro k hk
    exact ⟨fg_matches_inactive _ _ _ _ _ _ _ hfout k hk,
      fg_matches_inactive _ _ _ _ _ _ _ hgout k hk⟩

#print axioms fg_one_matches_spec
#print axioms fg_all_matches_spec
#print axioms update_fg_62_var_spec
end UdonVerify.CommonSigned62
