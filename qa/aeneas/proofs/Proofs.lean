import Word.Funs

open Aeneas Std Result
open zakura_udon.field.pasta.word

set_option maxHeartbeats 2000000
set_option exponentiation.threshold 500

/-- All three limbs may range over every u64 value. -/
@[step]
theorem adc_spec (lhs rhs carry : U64) :
    adc lhs rhs carry ⦃ result =>
      result.1.val = (lhs.val + rhs.val + carry.val) % 2^64 ∧
      result.2.val = (lhs.val + rhs.val + carry.val) / 2^64 ⦄ := by
  unfold adc
  step*
  all_goals simp_all [UScalar.cast_val_eq, Nat.shiftRight_eq_div_pow]
  all_goals scalar_tac

/-- The multiply-accumulate is exact for arbitrary u64 limbs. -/
@[step]
theorem mac_spec (accumulator lhs rhs carry : U64) :
    mac accumulator lhs rhs carry ⦃ result =>
      result.1.val = (lhs.val * rhs.val + accumulator.val + carry.val) % 2^64 ∧
      result.2.val = (lhs.val * rhs.val + accumulator.val + carry.val) / 2^64 ⦄ := by
  have hlhs : lhs.val % 2^128 = lhs.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hrhs : rhs.val % 2^128 = rhs.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hacc : accumulator.val % 2^128 = accumulator.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hcarry : carry.val % 2^128 = carry.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hproduct : lhs.val * rhs.val ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by scalar_tac) (by scalar_tac)
  have hbound : lhs.val * rhs.val + accumulator.val + carry.val < 2^128 := by
    scalar_tac
  unfold mac
  step*
  all_goals simp_all only [UScalar.cast_val_eq, UScalarTy.numBits,
    Nat.shiftRight_eq_div_pow]
  all_goals scalar_tac

/-- Subtraction propagates one borrow bit and preserves the integer identity. -/
@[step]
theorem sbb_spec (lhs rhs borrow : U64) (hborrow : borrow.val ≤ 1) :
    sbb lhs rhs borrow ⦃ result =>
      result.2.val ≤ 1 ∧
      result.1.val + rhs.val + borrow.val = lhs.val + 2^64 * result.2.val ⦄ := by
  unfold sbb
  step*
  all_goals split_ifs at * <;> simp_all [U64.size] <;> scalar_tac

#print axioms adc_spec
#print axioms mac_spec
#print axioms sbb_spec
