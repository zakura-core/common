import CommonComba.Funs
import NativeProductWords

open Aeneas Std Result

namespace UdonVerify.CommonComba
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev BatchColumn := Aeneas.Std.Array U64 3#usize

def batchColumnInteger (column : BatchColumn) : Nat :=
  column[0]!.val + B * column[1]!.val + B ^ 2 * column[2]!.val

theorem batch_overflowing_add_result (lhs rhs : U64) :
    ∃ (low : U64) (carry : Bool), core.num.U64.overflowing_add lhs rhs = (low, carry) ∧
      low.val + B * carry.toNat = lhs.val + rhs.val := by
  let out := core.num.U64.overflowing_add lhs rhs
  refine ⟨out.1, out.2, rfl, ?_⟩
  have h := core.num.U64.overflowing_add_eq lhs rhs
  change (if lhs.val + rhs.val > UScalar.max .U64 then
    out.1.val + UScalar.size .U64 = lhs.val + rhs.val ∧ out.2 = true
    else out.1.val = lhs.val + rhs.val ∧ out.2 = false) at h
  split_ifs at h with hcarry
  · rw [h.2]
    simpa only [Bool.toNat_true, mul_one, B, UScalar.size, UScalarTy.U64_numBits_eq] using h.1
  · rw [h.2]
    simpa only [Bool.toNat_false, mul_zero, add_zero] using h.1

theorem batch_bool_bound (flag : Bool) : flag.toNat ≤ 1 := by cases flag <;> decide

@[step]
theorem batch_start_column_spec (accumulator carryLow carryHigh : U64) :
    CommonComba.field.pasta.products.start_column accumulator carryLow carryHigh ⦃ out =>
      batchColumnInteger out = accumulator.val + carryLow.val + B * carryHigh.val ∧
        batchColumnInteger out < 2 * B ^ 2 ⦄ := by
  unfold CommonComba.field.pasta.products.start_column
  simp only [lift, bind_ok, Std.uncurry]
  obtain ⟨low, carry, hlowResult, hlow⟩ := batch_overflowing_add_result accumulator carryLow
  rw [hlowResult]
  simp only [Std.uncurry]
  obtain ⟨middle, high, hmiddleResult, hmiddle⟩ :=
    batch_overflowing_add_result carryHigh (UScalar.cast_fromBool .U64 carry)
  rw [hmiddleResult]
  simp only [Std.uncurry, WP.spec_ok]
  have hcarryWord := UScalar.cast_fromBool_val_eq .U64 carry
  have hhighWord := UScalar.cast_fromBool_val_eq .U64 high
  have hvalue : batchColumnInteger (Aeneas.Std.Array.make 3#usize
      [low, middle, UScalar.cast_fromBool .U64 high]) =
      accumulator.val + carryLow.val + B * carryHigh.val := by
    simp [batchColumnInteger, Array.make, hhighWord]
    rw [hcarryWord] at hmiddle
    norm_num [B] at hlow hmiddle ⊢
    omega
  refine ⟨hvalue, ?_⟩
  rw [hvalue]
  have ha := accumulator.hmax
  have hl := carryLow.hmax
  have hh := carryHigh.hmax
  norm_num [UScalar.max, UScalarTy.U64_numBits_eq, B] at *
  omega

#print axioms batch_overflowing_add_result
#print axioms batch_bool_bound
#print axioms batch_start_column_spec

end UdonVerify.CommonComba
