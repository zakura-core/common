import CommonFG62Flat2
import CommonFG62Value
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem fg_flat_2_spec (f g : Signed62)
    (t : CommonFG62.field.pasta.safegcd.Trans2x2)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix)
    (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hf : fgInputsBounded 2 f) (hg : fgInputsBounded 2 g)
    (hdivf : fgRowInteger t.u.val t.v.val f g 0 % signedRadix = 0)
    (hdivg : fgRowInteger t.q.val t.r.val f g 0 % signedRadix = 0) :
    fgFlat2 f g t ⦃ out =>
      fgRowMatches 2 t.u.val t.v.val f g f out.1 ∧
      fgRowMatches 2 t.q.val t.r.val f g g out.2 ⦄ := by
  have hpos : 0 ≤ signedRadix := by norm_num [signedRadix]
  have hf0 : |f[0]!.val| ≤ signedRadix := hf ⟨0, by decide⟩ (by decide)
  have hg0 : |g[0]!.val| ≤ signedRadix := hg ⟨0, by decide⟩ (by decide)
  have hf1 : |f[1]!.val| ≤ signedRadix := hf ⟨1, by decide⟩ (by decide)
  have hg1 : |g[1]!.val| ≤ signedRadix := hg ⟨1, by decide⟩ (by decide)
  unfold fgFlat2
  step -grind with (fg_row_term_spec t.u t.v f[0]! g[0]! huv hf0 hg0)
    as ⟨cf0, hcf0, hcf0b⟩
  step -grind with (fg_row_term_spec t.q t.r f[0]! g[0]! hqr hf0 hg0)
    as ⟨cg0, hcg0, hcg0b⟩
  have hzf := fg_row_low_zero cf0 (by rw [hcf0]; exact hdivf)
  have hzg := fg_row_low_zero cg0 (by rw [hcg0]; exact hdivg)
  step -grind
  step -grind
  step -grind with (fg_row_shift_spec cf0 (by omega)) as ⟨cf1, hcf1, hcf1b⟩
  step -grind with (fg_row_shift_spec cg0 (by omega)) as ⟨cg1, hcg1, hcg1b⟩
  have hfc0 : cf1.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 0 := by
    rw [hcf1, hcf0]
    rfl
  have hgc0 : cg1.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 0 := by
    rw [hcg1, hcg0]
    rfl
  step -grind with (fg_row_term_spec t.u t.v f[1]! g[1]! huv hf1 hg1)
    as ⟨tf1, htf1, htf1b⟩
  step -grind with (fg_row_add_spec cf1 tf1 hcf1b htf1b)
    as ⟨cf2, hcf2, hcf2b⟩
  step -grind with (fg_row_term_spec t.q t.r f[1]! g[1]! hqr hf1 hg1)
    as ⟨tg1, htg1, htg1b⟩
  step -grind with (fg_row_add_spec cg1 tg1 hcg1b htg1b)
    as ⟨cg2, hcg2, hcg2b⟩
  have hfa1 : cf2.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 0 +
      fgRowInteger t.u.val t.v.val f g 1 := by
    rw [hcf2, hfc0, htf1]
    rfl
  have hga1 : cg2.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 0 +
      fgRowInteger t.q.val t.r.val f g 1 := by
    rw [hcg2, hgc0, htg1]
    rfl
  have hfd1 : (fgRowDigit cf2).val = fgStoredDigit
      (fgRowInteger t.u.val t.v.val f g) 2 0 := by
    rw [(fg_row_digit_value cf2).1, hfa1]
    rfl
  have hgd1 : (fgRowDigit cg2).val = fgStoredDigit
      (fgRowInteger t.q.val t.r.val f g) 2 0 := by
    rw [(fg_row_digit_value cg2).1, hga1]
    rfl
  step -grind with (fg_row_shift_spec cf2 hcf2b) as ⟨cf3, hcf3, hcf3b⟩
  step -grind with (fg_row_shift_spec cg2 hcg2b) as ⟨cg3, hcg3, hcg3b⟩
  have hfc1 : cf3.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 1 := by
    rw [hcf3, hfa1]
    rfl
  have hgc1 : cg3.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 1 := by
    rw [hcg3, hga1]
    rfl
  step -grind with (fg_row_tail_spec cf3 hcf3b) as ⟨ft, hft⟩
  step -grind with (fg_row_tail_spec cg3 hcg3b) as ⟨gt, hgt⟩
  have hftv := hft.trans hfc1
  have hgtv := hgt.trans hgc1
  try simp only [WP.spec_ok]
  constructor
  · intro k
    fin_cases k <;> simp [hfd1, hftv, fgStoredDigit]
  · intro k
    fin_cases k <;> simp [hgd1, hgtv, fgStoredDigit]

#print axioms fg_flat_2_spec
end UdonVerify.CommonSigned62
