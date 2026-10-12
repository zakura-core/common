import CommonCoeffStart
import CommonFG62Sparse

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem coeff_accumulator_i128 (value : Int)
    (h : |value| ≤ 3 * signedRadix ^ 2 + 3 * signedRadix + 5) :
    -(2 ^ 127) ≤ value ∧ value < 2 ^ 127 := by
  have hb := abs_le.mp h
  norm_num only [signedRadix] at hb ⊢
  constructor <;> omega

def coeffModTerm (modulus correction : I64) : Result I128 := do
  let m ← lift (core.convert.num.FromI128I64.from modulus)
  let c ← lift (core.convert.num.FromI128I64.from correction)
  m * c

@[step]
theorem coeff_mod_term_spec (modulus correction : I64)
    (hm : |modulus.val| ≤ signedRadix) (hc : |correction.val| ≤ 2 * signedRadix) :
    coeffModTerm modulus correction ⦃ out =>
      out.val = modulus.val * correction.val ∧ |out.val| ≤ 2 * signedRadix ^ 2 ⦄ := by
  have hp : |modulus.val * correction.val| ≤ 2 * signedRadix ^ 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg modulus.val, abs_nonneg correction.val]
  have hfit := coeff_accumulator_i128 (modulus.val * correction.val)
    (by norm_num only [signedRadix] at hp ⊢; omega)
  unfold coeffModTerm
  simp only [lift, bind_ok]
  step +scalarTac -grind with I128.mul_spec as ⟨out, hout⟩
  simp only [core.convert.num.FromI128I64.from_val_eq] at hout
  exact ⟨hout, by rw [hout]; exact hp⟩

@[step]
theorem coeff_add_row_spec (carry term : I128)
    (hc : |carry.val| ≤ 3 * signedRadix + 5) (ht : |term.val| ≤ signedRadix ^ 2) :
    carry + term ⦃ out => out.val = carry.val + term.val ∧
      |out.val| ≤ signedRadix ^ 2 + 3 * signedRadix + 5 ⦄ := by
  have hs := abs_add_le carry.val term.val
  have hb : |carry.val + term.val| ≤ signedRadix ^ 2 + 3 * signedRadix + 5 := by omega
  have hfit := coeff_accumulator_i128 (carry.val + term.val)
    (by norm_num only [signedRadix] at hb ⊢; omega)
  step +scalarTac -grind with I128.add_spec as ⟨out, hout⟩
  exact ⟨hout, by rw [hout]; exact hb⟩

@[step]
theorem coeff_add_mod_spec (row term : I128)
    (hr : |row.val| ≤ signedRadix ^ 2 + 3 * signedRadix + 5)
    (ht : |term.val| ≤ 2 * signedRadix ^ 2) :
    row + term ⦃ out => out.val = row.val + term.val ∧
      |out.val| ≤ 3 * signedRadix ^ 2 + 3 * signedRadix + 5 ⦄ := by
  have hs := abs_add_le row.val term.val
  have hb : |row.val + term.val| ≤ 3 * signedRadix ^ 2 + 3 * signedRadix + 5 := by omega
  have hfit := coeff_accumulator_i128 (row.val + term.val) hb
  step +scalarTac -grind with I128.add_spec as ⟨out, hout⟩
  exact ⟨hout, by rw [hout]; exact hb⟩

@[step]
theorem coeff_shift_spec (value : I128)
    (h : |value.val| ≤ 3 * signedRadix ^ 2 + 3 * signedRadix + 5) :
    value >>> 62#i32 ⦃ out => out.val = value.val / signedRadix ∧
      |out.val| ≤ 3 * signedRadix + 5 ⦄ := by
  step -grind with I128.ShiftRight_IScalar_spec as ⟨out, hval, _⟩
  have hv : out.val = value.val / signedRadix := by
    simpa only [show (62#i32).toNat = 62 from by decide, Int.shiftRight_eq_div_pow,
      signedRadix, Nat.cast_pow, Nat.cast_ofNat] using hval
  refine ⟨hv, ?_⟩
  rw [hv, abs_le]
  have hb := abs_le.mp h
  norm_num only [signedRadix] at hb ⊢
  constructor <;> omega

@[step]
theorem coeff_top_term_spec (u v d e : I64)
    (hrow : |u.val| + |v.val| ≤ signedRadix) (hd : |d.val| ≤ 256) (he : |e.val| ≤ 256) :
    fgRowTerm u v d e ⦃ out => out.val = u.val * d.val + v.val * e.val ∧
      |out.val| ≤ 256 * signedRadix ⦄ := by
  have hbD : |d.val| ≤ signedRadix := by norm_num only [signedRadix]; omega
  have hbE : |e.val| ≤ signedRadix := by norm_num only [signedRadix]; omega
  have hpD := mul_le_mul_of_nonneg_left hd (abs_nonneg u.val)
  have hpE := mul_le_mul_of_nonneg_left he (abs_nonneg v.val)
  have hs := abs_add_le (u.val * d.val) (v.val * e.val)
  rw [abs_mul, abs_mul] at hs
  have htop : |u.val * d.val + v.val * e.val| ≤ 256 * signedRadix := by nlinarith
  apply WP.spec_mono (fg_row_term_spec u v d e hrow hbD hbE)
  intro out hout
  exact ⟨hout.1, by rw [hout.1]; exact htop⟩

@[step]
theorem coeff_top_add_row_spec (carry term : I128)
    (hc : |carry.val| ≤ 3 * signedRadix + 5) (ht : |term.val| ≤ 256 * signedRadix) :
    carry + term ⦃ out => out.val = carry.val + term.val ∧ |out.val| ≤ 259 * signedRadix + 5 ⦄ := by
  have hs := abs_add_le carry.val term.val
  have hb : |carry.val + term.val| ≤ 259 * signedRadix + 5 := by omega
  have hfit := coeff_accumulator_i128 (carry.val + term.val)
    (by norm_num only [signedRadix] at hb ⊢; omega)
  step +scalarTac -grind with I128.add_spec as ⟨out, hout⟩
  exact ⟨hout, by rw [hout]; exact hb⟩

@[step]
theorem coeff_top_add_mod_spec (row term : I128)
    (hr : |row.val| ≤ 259 * signedRadix + 5) (ht : |term.val| ≤ 128 * signedRadix) :
    row + term ⦃ out => out.val = row.val + term.val ∧ |out.val| ≤ 387 * signedRadix + 5 ⦄ := by
  have hs := abs_add_le row.val term.val
  have hb : |row.val + term.val| ≤ 387 * signedRadix + 5 := by omega
  have hfit := coeff_accumulator_i128 (row.val + term.val)
    (by norm_num only [signedRadix] at hb ⊢; omega)
  step +scalarTac -grind with I128.add_spec as ⟨out, hout⟩
  exact ⟨hout, by rw [hout]; exact hb⟩

@[step]
theorem coeff_top_shift_spec (value : I128) (h : |value.val| ≤ 387 * signedRadix + 5) :
    value >>> 62#i32 ⦃ out => out.val = value.val / signedRadix ∧ |out.val| ≤ 388 ⦄ := by
  step -grind with I128.ShiftRight_IScalar_spec as ⟨out, hval, _⟩
  have hv : out.val = value.val / signedRadix := by
    simpa only [show (62#i32).toNat = 62 from by decide, Int.shiftRight_eq_div_pow,
      signedRadix, Nat.cast_pow, Nat.cast_ofNat] using hval
  refine ⟨hv, ?_⟩
  rw [hv, abs_le]
  have hb := abs_le.mp h
  norm_num only [signedRadix] at hb ⊢
  constructor <;> omega

#print axioms coeff_accumulator_i128
#print axioms coeff_mod_term_spec
#print axioms coeff_add_row_spec
#print axioms coeff_add_mod_spec
#print axioms coeff_shift_spec
#print axioms coeff_top_term_spec
#print axioms coeff_top_add_row_spec
#print axioms coeff_top_add_mod_spec
#print axioms coeff_top_shift_spec
end UdonVerify.CommonSigned62
