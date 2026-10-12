import CommonFG62Update
import CommonFG62First.Funs

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def fgSparseTerm (u v gi : I64) (shift : I32) : Result I128 := do
  let left0 ← lift (core.convert.num.FromI128I64.from u)
  let left ← left0 <<< shift
  let right0 ← lift (core.convert.num.FromI128I64.from v)
  let right1 ← lift (core.convert.num.FromI128I64.from gi)
  let right ← right0 * right1
  left + right

def fgZeroTerm (v gi : I64) : Result I128 := do
  let left ← lift (core.convert.num.FromI128I64.from v)
  let right ← lift (core.convert.num.FromI128I64.from gi)
  left * right

@[step]
theorem fg_widen_shift_spec (u : I64) (shift : I32)
    (hshift : shift = 1#i32 ∨ shift = 6#i32) :
    (core.convert.num.FromI128I64.from u <<< shift) ⦃ out =>
      out.val = u.val * (2 : Int) ^ shift.toNat ⦄ := by
  rcases hshift with rfl | rfl
  all_goals
    step -grind with I128.ShiftLeft_IScalar_spec as ⟨out, hvalue, hbits⟩
    simp only [core.convert.num.FromI128I64.from_val_eq, Int.shiftLeft_eq,
      I128.size, I128.numBits] at hvalue
    rw [hvalue]
    apply Arith.Int.bmod_pow2_eq_of_inBounds 127 <;> scalar_tac

@[step]
theorem fg_sparse_term_spec (u v fi gi : I64) (shift : I32)
    (hshift : shift = 1#i32 ∨ shift = 6#i32)
    (hfi : fi.val = (2 : Int) ^ shift.toNat)
    (huv : |u.val| + |v.val| ≤ signedRadix)
    (hf : |fi.val| ≤ signedRadix) (hg : |gi.val| ≤ signedRadix) :
    fgSparseTerm u v gi shift ⦃ out =>
      out.val = u.val * fi.val + v.val * gi.val ∧ |out.val| ≤ signedRadix ^ 2 ⦄ := by
  have hv : |v.val| ≤ signedRadix := by have h := abs_nonneg u.val; omega
  have hproduct : |v.val * gi.val| ≤ signedRadix ^ 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg v.val, abs_nonneg gi.val]
  have hrow := row_term_bound u.val v.val fi.val gi.val huv hf hg
  have hbp := row_accumulator_i128 (v.val * gi.val)
    (by norm_num [signedRadix] at hproduct ⊢; omega)
  have hbr := row_accumulator_i128 (u.val * fi.val + v.val * gi.val)
    (by norm_num [signedRadix] at hrow ⊢; omega)
  unfold fgSparseTerm
  simp only [lift, bind_ok]
  step -grind with (fg_widen_shift_spec u shift hshift) as ⟨left, hleft⟩
  step +scalarTac -grind with I128.mul_spec as ⟨right, hright⟩
  simp only [core.convert.num.FromI128I64.from_val_eq] at hright
  step +scalarTac -grind with I128.add_spec as ⟨out, hout⟩
  rw [hout, hleft, ← hfi, hright]
  exact ⟨rfl, hrow⟩

@[step]
theorem fg_zero_term_spec (u v fi gi : I64) (hfi : fi.val = 0)
    (huv : |u.val| + |v.val| ≤ signedRadix)
    (hf : |fi.val| ≤ signedRadix) (hg : |gi.val| ≤ signedRadix) :
    fgZeroTerm v gi ⦃ out =>
      out.val = u.val * fi.val + v.val * gi.val ∧ |out.val| ≤ signedRadix ^ 2 ⦄ := by
  have hrow := row_term_bound u.val v.val fi.val gi.val huv hf hg
  rw [hfi, mul_zero, zero_add] at hrow
  have hb := row_accumulator_i128 (v.val * gi.val)
    (by norm_num [signedRadix] at hrow ⊢; omega)
  unfold fgZeroTerm
  simp only [lift, bind_ok]
  step +scalarTac -grind with I128.mul_spec as ⟨out, hout⟩
  simp only [core.convert.num.FromI128I64.from_val_eq] at hout
  rw [hout, hfi, mul_zero, zero_add]
  exact ⟨rfl, hrow⟩

theorem fg_array_self_eq (a : Signed62) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqI64 a a = ok true := by
  have aux (values : List I64) :
      List.allM (fun (x, y) => ok (decide (x.val = y.val)))
        (values.zip values) = ok true := by
    induction values with
    | nil => rfl
    | cons head tail ih =>
      simp [List.allM, Bind.bind, ih]
  rw [core.array.equality.PartialEqArray.eq, if_pos rfl]
  simpa [core.cmp.PartialEqI64, core.cmp.impls.PartialEqI64.ne,
    liftFun2, Bind.bind] using aux a.val

theorem fg_first_mask_eq :
    CommonFG62First.field.pasta.safegcd.MASK62 = ok 4611686018427387903#u64 := by
  have h : CommonFG62First.field.pasta.safegcd.MASK62 =
      Signed62Native.field.pasta.safegcd.MASK62 := by
    unfold CommonFG62First.field.pasta.safegcd.MASK62 Signed62Native.field.pasta.safegcd.MASK62
    rfl
  exact h.trans mask62_eq

theorem active62_value_five (a : Signed62) : active62Value a 5 = signed62Value a := by
  norm_num [active62Value, signed62Value, Finset.sum_range_succ]

#print axioms fg_widen_shift_spec
#print axioms fg_sparse_term_spec
#print axioms fg_zero_term_spec
#print axioms fg_array_self_eq
#print axioms fg_first_mask_eq
#print axioms active62_value_five
end UdonVerify.CommonSigned62
