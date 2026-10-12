import CommonFG62Math
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def fgRowTerm (u v fi gi : I64) : Result I128 := do
  let u128 ← lift (core.convert.num.FromI128I64.from u)
  let f128 ← lift (core.convert.num.FromI128I64.from fi)
  let first ← u128*f128
  let v128 ← lift (core.convert.num.FromI128I64.from v)
  let g128 ← lift (core.convert.num.FromI128I64.from gi)
  let second ← v128*g128
  first+second

@[step]
theorem fg_row_term_spec (u v fi gi : I64)
    (huv : |u.val|+|v.val| ≤ signedRadix)
    (hf : |fi.val| ≤ signedRadix) (hg : |gi.val| ≤ signedRadix) :
    fgRowTerm u v fi gi ⦃ out => out.val=u.val*fi.val+v.val*gi.val ∧
      |out.val| ≤ signedRadix^2 ⦄ := by
  have hu : |u.val| ≤ signedRadix := by have h := abs_nonneg v.val;omega
  have hv : |v.val| ≤ signedRadix := by have h := abs_nonneg u.val;omega
  have hfirst : |u.val*fi.val| ≤ signedRadix^2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg u.val,abs_nonneg fi.val]
  have hsecond : |v.val*gi.val| ≤ signedRadix^2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg v.val,abs_nonneg gi.val]
  have hrow := row_term_bound u.val v.val fi.val gi.val huv hf hg
  have hb1 := row_accumulator_i128 (u.val*fi.val) (by norm_num [signedRadix] at hfirst ⊢;omega)
  have hb2 := row_accumulator_i128 (v.val*gi.val) (by norm_num [signedRadix] at hsecond ⊢;omega)
  have hbr := row_accumulator_i128 (u.val*fi.val+v.val*gi.val) (by norm_num [signedRadix] at hrow ⊢;omega)
  unfold fgRowTerm
  simp only [lift,bind_ok]
  step +scalarTac -grind with I128.mul_spec as ⟨first,hval1⟩
  step +scalarTac -grind with I128.mul_spec as ⟨second,hval2⟩
  step +scalarTac -grind with I128.add_spec as ⟨out,hout⟩
  simp only [core.convert.num.FromI128I64.from_val_eq] at hval1 hval2
  rw [hout,hval1,hval2]
  exact ⟨rfl,hrow⟩

@[step]
theorem fg_row_add_spec (carry term : I128)
    (hc : |carry.val| ≤ signedRadix+2) (ht : |term.val| ≤ signedRadix^2) :
    (carry+term) ⦃ out => out.val=carry.val+term.val ∧
      |out.val| ≤ signedRadix^2+signedRadix+2 ⦄ := by
  have h := row_accumulator_bound carry.val term.val hc ht
  have hb := row_accumulator_i128 (carry.val+term.val) h
  step +scalarTac -grind with I128.add_spec as ⟨out,hout⟩
  exact ⟨hout,by rw [hout];exact h⟩

@[step]
theorem fg_row_shift_spec (value : I128)
    (h : |value.val| ≤ signedRadix^2+signedRadix+2) :
    (value >>> 62#i32) ⦃ out => out.val=value.val/signedRadix ∧
      |out.val| ≤ signedRadix+2 ⦄ := by
  step -grind with I128.ShiftRight_IScalar_spec as ⟨out,hval,hbv⟩
  have heq : out.val=value.val/signedRadix := by
    simpa only [show (62#i32).toNat=62 from by decide,Int.shiftRight_eq_div_pow,signedRadix,Nat.cast_pow,Nat.cast_ofNat] using hval
  exact ⟨heq,by rw [heq];exact row_carry_bound value.val h⟩

#print axioms fg_row_term_spec
#print axioms fg_row_add_spec
#print axioms fg_row_shift_spec
end UdonVerify.CommonSigned62
