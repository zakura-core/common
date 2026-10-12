import CommonFG62FirstFlat
import CommonFG62Value
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem fg_first_flat_spec (f g : Signed62)
    (t : CommonFG62First.field.pasta.safegcd.Trans2x2)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix)
    (hqr : |t.q.val| + |t.r.val| ≤ signedRadix)
    (hshape : f[2]!.val = 2 ∧ f[3]!.val = 0 ∧ f[4]!.val = 64)
    (hf : fgInputsBounded 5 f) (hg : fgInputsBounded 5 g)
    (hdivf : fgRowInteger t.u.val t.v.val f g 0 % signedRadix = 0)
    (hdivg : fgRowInteger t.q.val t.r.val f g 0 % signedRadix = 0) :
    fgFirstFlat f g t ⦃ out =>
      fgRowMatches 5 t.u.val t.v.val f g f out.1 ∧
      fgRowMatches 5 t.q.val t.r.val f g g out.2 ⦄ := by
  have hpos : 0 ≤ signedRadix := by norm_num [signedRadix]
  have hf0 : |f[0]!.val| ≤ signedRadix := hf ⟨0, by decide⟩ (by decide)
  have hg0 : |g[0]!.val| ≤ signedRadix := hg ⟨0, by decide⟩ (by decide)
  have hf1 : |f[1]!.val| ≤ signedRadix := hf ⟨1, by decide⟩ (by decide)
  have hg1 : |g[1]!.val| ≤ signedRadix := hg ⟨1, by decide⟩ (by decide)
  have hf2 : |f[2]!.val| ≤ signedRadix := hf ⟨2, by decide⟩ (by decide)
  have hg2 : |g[2]!.val| ≤ signedRadix := hg ⟨2, by decide⟩ (by decide)
  have hf3 : |f[3]!.val| ≤ signedRadix := hf ⟨3, by decide⟩ (by decide)
  have hg3 : |g[3]!.val| ≤ signedRadix := hg ⟨3, by decide⟩ (by decide)
  have hf4 : |f[4]!.val| ≤ signedRadix := hf ⟨4, by decide⟩ (by decide)
  have hg4 : |g[4]!.val| ≤ signedRadix := hg ⟨4, by decide⟩ (by decide)
  unfold fgFirstFlat
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
      (fgRowInteger t.u.val t.v.val f g) 5 0 := by
    rw [(fg_row_digit_value cf2).1, hfa1]
    rfl
  have hgd1 : (fgRowDigit cg2).val = fgStoredDigit
      (fgRowInteger t.q.val t.r.val f g) 5 0 := by
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
  step -grind with (fg_sparse_term_spec t.u t.v f[2]! g[2]! 1#i32
    (Or.inl rfl) (by simpa [IScalar.toNat] using hshape.1)
    huv hf2 hg2)
    as ⟨tf2, htf2, htf2b⟩
  step -grind with (fg_row_add_spec cf3 tf2 hcf3b htf2b)
    as ⟨cf4, hcf4, hcf4b⟩
  step -grind with (fg_sparse_term_spec t.q t.r f[2]! g[2]! 1#i32
    (Or.inl rfl) (by simpa [IScalar.toNat] using hshape.1)
    hqr hf2 hg2)
    as ⟨tg2, htg2, htg2b⟩
  step -grind with (fg_row_add_spec cg3 tg2 hcg3b htg2b)
    as ⟨cg4, hcg4, hcg4b⟩
  have hfa2 : cf4.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 1 +
      fgRowInteger t.u.val t.v.val f g 2 := by
    rw [hcf4, hfc1, htf2]
    rfl
  have hga2 : cg4.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 1 +
      fgRowInteger t.q.val t.r.val f g 2 := by
    rw [hcg4, hgc1, htg2]
    rfl
  have hfd2 : (fgRowDigit cf4).val = fgStoredDigit
      (fgRowInteger t.u.val t.v.val f g) 5 1 := by
    rw [(fg_row_digit_value cf4).1, hfa2]
    rfl
  have hgd2 : (fgRowDigit cg4).val = fgStoredDigit
      (fgRowInteger t.q.val t.r.val f g) 5 1 := by
    rw [(fg_row_digit_value cg4).1, hga2]
    rfl
  step -grind with (fg_row_shift_spec cf4 hcf4b) as ⟨cf5, hcf5, hcf5b⟩
  step -grind with (fg_row_shift_spec cg4 hcg4b) as ⟨cg5, hcg5, hcg5b⟩
  have hfc2 : cf5.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 2 := by
    rw [hcf5, hfa2]
    rfl
  have hgc2 : cg5.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 2 := by
    rw [hcg5, hga2]
    rfl
  step -grind with (fg_zero_term_spec t.u t.v f[3]! g[3]! hshape.2.1 huv hf3 hg3)
    as ⟨tf3, htf3, htf3b⟩
  step -grind with (fg_row_add_spec cf5 tf3 hcf5b htf3b)
    as ⟨cf6, hcf6, hcf6b⟩
  step -grind with (fg_zero_term_spec t.q t.r f[3]! g[3]! hshape.2.1 hqr hf3 hg3)
    as ⟨tg3, htg3, htg3b⟩
  step -grind with (fg_row_add_spec cg5 tg3 hcg5b htg3b)
    as ⟨cg6, hcg6, hcg6b⟩
  have hfa3 : cf6.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 2 +
      fgRowInteger t.u.val t.v.val f g 3 := by
    rw [hcf6, hfc2, htf3]
    rfl
  have hga3 : cg6.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 2 +
      fgRowInteger t.q.val t.r.val f g 3 := by
    rw [hcg6, hgc2, htg3]
    rfl
  have hfd3 : (fgRowDigit cf6).val = fgStoredDigit
      (fgRowInteger t.u.val t.v.val f g) 5 2 := by
    rw [(fg_row_digit_value cf6).1, hfa3]
    rfl
  have hgd3 : (fgRowDigit cg6).val = fgStoredDigit
      (fgRowInteger t.q.val t.r.val f g) 5 2 := by
    rw [(fg_row_digit_value cg6).1, hga3]
    rfl
  step -grind with (fg_row_shift_spec cf6 hcf6b) as ⟨cf7, hcf7, hcf7b⟩
  step -grind with (fg_row_shift_spec cg6 hcg6b) as ⟨cg7, hcg7, hcg7b⟩
  have hfc3 : cf7.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 3 := by
    rw [hcf7, hfa3]
    rfl
  have hgc3 : cg7.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 3 := by
    rw [hcg7, hga3]
    rfl
  step -grind with (fg_sparse_term_spec t.u t.v f[4]! g[4]! 6#i32
    (Or.inr rfl) (by simpa [IScalar.toNat] using hshape.2.2)
    huv hf4 hg4)
    as ⟨tf4, htf4, htf4b⟩
  step -grind with (fg_row_add_spec cf7 tf4 hcf7b htf4b)
    as ⟨cf8, hcf8, hcf8b⟩
  step -grind with (fg_sparse_term_spec t.q t.r f[4]! g[4]! 6#i32
    (Or.inr rfl) (by simpa [IScalar.toNat] using hshape.2.2)
    hqr hf4 hg4)
    as ⟨tg4, htg4, htg4b⟩
  step -grind with (fg_row_add_spec cg7 tg4 hcg7b htg4b)
    as ⟨cg8, hcg8, hcg8b⟩
  have hfa4 : cf8.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 3 +
      fgRowInteger t.u.val t.v.val f g 4 := by
    rw [hcf8, hfc3, htf4]
    rfl
  have hga4 : cg8.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 3 +
      fgRowInteger t.q.val t.r.val f g 4 := by
    rw [hcg8, hgc3, htg4]
    rfl
  have hfd4 : (fgRowDigit cf8).val = fgStoredDigit
      (fgRowInteger t.u.val t.v.val f g) 5 3 := by
    rw [(fg_row_digit_value cf8).1, hfa4]
    rfl
  have hgd4 : (fgRowDigit cg8).val = fgStoredDigit
      (fgRowInteger t.q.val t.r.val f g) 5 3 := by
    rw [(fg_row_digit_value cg8).1, hga4]
    rfl
  step -grind with (fg_row_shift_spec cf8 hcf8b) as ⟨cf9, hcf9, hcf9b⟩
  step -grind with (fg_row_shift_spec cg8 hcg8b) as ⟨cg9, hcg9, hcg9b⟩
  have hfc4 : cf9.val = fgCarry (fgRowInteger t.u.val t.v.val f g) 4 := by
    rw [hcf9, hfa4]
    rfl
  have hgc4 : cg9.val = fgCarry (fgRowInteger t.q.val t.r.val f g) 4 := by
    rw [hcg9, hga4]
    rfl
  step -grind with (fg_row_tail_spec cf9 hcf9b) as ⟨ft, hft⟩
  step -grind with (fg_row_tail_spec cg9 hcg9b) as ⟨gt, hgt⟩
  have hftv := hft.trans hfc4
  have hgtv := hgt.trans hgc4
  try simp only [WP.spec_ok]
  constructor
  · intro k
    fin_cases k <;> simp [hfd1, hfd2, hfd3, hfd4, hftv, fgStoredDigit]
  · intro k
    fin_cases k <;> simp [hgd1, hgd2, hgd3, hgd4, hgtv, fgStoredDigit]

#print axioms fg_first_flat_spec
end UdonVerify.CommonSigned62
