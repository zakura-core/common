import Proofs

open Aeneas Std Result
open zakura_udon.field.pasta.word

namespace CommonVerify

set_option maxHeartbeats 2000000
set_option exponentiation.threshold 500

theorem overflowing_add_identity (lhs rhs : U64) :
    let out := Aeneas.Std.core.num.U64.overflowing_add lhs rhs
    out.1.val + 2^64 * out.2.toNat = lhs.val + rhs.val := by
  dsimp only
  have h := Aeneas.Std.core.num.U64.overflowing_add_eq lhs rhs
  split_ifs at h with hoverflow
  · rw [h.2]
    simpa [U64.size, U64.numBits, UScalar.size, UScalarTy.U64_numBits_eq] using h.1
  · rw [h.2]
    simpa using h.1

theorem overflowing_sub_identity (lhs rhs : U64) :
    let out := Aeneas.Std.core.num.U64.overflowing_sub lhs rhs
    out.1.val + rhs.val = lhs.val + 2^64 * out.2.toNat := by
  dsimp only
  have h := Aeneas.Std.core.num.U64.overflowing_sub_eq lhs rhs
  split_ifs at h with hborrow
  · rw [h.2]
    simpa [U64.size, U64.numBits, UScalar.size, UScalarTy.U64_numBits_eq] using h.1
  · rw [h.2]
    simp only [Bool.toNat_false, mul_zero, add_zero]
    omega

theorem bool_or_disjoint (first second : Bool)
    (h : ¬ (first = true ∧ second = true)) :
    (first || second).toNat = first.toNat + second.toNat := by
  cases first <;> cases second <;> simp_all

theorem bool_bound (flag : Bool) : flag.toNat ≤ 1 := by
  cases flag <;> decide

/-- The two carry flags satisfy the precondition of Rust's disjoint_bitor intrinsic. -/
theorem carrying_add_flags_disjoint (lhs rhs : U64) (carry : Bool) :
    let first := Aeneas.Std.core.num.U64.overflowing_add lhs rhs
    let second := Aeneas.Std.core.num.U64.overflowing_add first.1
      (UScalar.cast_fromBool .U64 carry)
    ¬ (first.2 = true ∧ second.2 = true) := by
  dsimp only
  intro h
  have hfirst := overflowing_add_identity lhs rhs
  have hsecond := overflowing_add_identity
    (Aeneas.Std.core.num.U64.overflowing_add lhs rhs).1
    (UScalar.cast_fromBool .U64 carry)
  dsimp only at hfirst hsecond
  rw [h.1] at hfirst
  rw [h.2] at hsecond
  have hcarry := bool_bound carry
  have hlhs := lhs.hmax
  have hrhs := rhs.hmax
  simp only [Bool.toNat_true, mul_one, UScalar.cast_fromBool_val_eq] at hfirst hsecond
  norm_num [UScalar.max, UScalarTy.U64_numBits_eq] at hlhs hrhs hfirst hsecond
  omega

/-- The two borrow flags satisfy the precondition of Rust's disjoint_bitor intrinsic. -/
theorem borrowing_sub_flags_disjoint (lhs rhs : U64) (borrow : Bool) :
    let first := Aeneas.Std.core.num.U64.overflowing_sub lhs rhs
    let second := Aeneas.Std.core.num.U64.overflowing_sub first.1
      (UScalar.cast_fromBool .U64 borrow)
    ¬ (first.2 = true ∧ second.2 = true) := by
  dsimp only
  intro h
  have hfirst := overflowing_sub_identity lhs rhs
  have hsecond := overflowing_sub_identity
    (Aeneas.Std.core.num.U64.overflowing_sub lhs rhs).1
    (UScalar.cast_fromBool .U64 borrow)
  dsimp only at hfirst hsecond
  rw [h.1] at hfirst
  rw [h.2] at hsecond
  have hborrow := bool_bound borrow
  have hrhs := rhs.hmax
  have hout := (Aeneas.Std.core.num.U64.overflowing_sub
    (Aeneas.Std.core.num.U64.overflowing_sub lhs rhs).1
    (UScalar.cast_fromBool .U64 borrow)).1.hmax
  simp only [Bool.toNat_true, mul_one, UScalar.cast_fromBool_val_eq] at hfirst hsecond
  norm_num [UScalar.max, UScalarTy.U64_numBits_eq] at hrhs hout hfirst hsecond
  omega

@[step]
theorem carrying_add_spec (lhs rhs : U64) (carry : Bool) :
    _root_.core.num.U64.carrying_add lhs rhs carry ⦃ out =>
      out.1.val + 2^64 * out.2.toNat = lhs.val + rhs.val + carry.toNat ⦄ := by
  unfold _root_.core.num.U64.carrying_add
  simp only [lift, bind_ok, Std.uncurry, WP.spec_ok]
  rw [bool_or_disjoint _ _ (carrying_add_flags_disjoint lhs rhs carry)]
  have hfirst := overflowing_add_identity lhs rhs
  have hsecond := overflowing_add_identity
    (Aeneas.Std.core.num.U64.overflowing_add lhs rhs).1
    (UScalar.cast_fromBool .U64 carry)
  rw [UScalar.cast_fromBool_val_eq] at hsecond
  omega

@[step]
theorem borrowing_sub_spec (lhs rhs : U64) (borrow : Bool) :
    _root_.core.num.U64.borrowing_sub lhs rhs borrow ⦃ out =>
      out.1.val + rhs.val + borrow.toNat = lhs.val + 2^64 * out.2.toNat ⦄ := by
  unfold _root_.core.num.U64.borrowing_sub
  simp only [lift, bind_ok, Std.uncurry, WP.spec_ok]
  rw [bool_or_disjoint _ _ (borrowing_sub_flags_disjoint lhs rhs borrow)]
  have hfirst := overflowing_sub_identity lhs rhs
  have hsecond := overflowing_sub_identity
    (Aeneas.Std.core.num.U64.overflowing_sub lhs rhs).1
    (UScalar.cast_fromBool .U64 borrow)
  rw [UScalar.cast_fromBool_val_eq] at hsecond
  omega

@[step]
theorem carry_add_spec (lhs rhs : U64) (carry : Bool) :
    carry_add lhs rhs carry ⦃ out =>
      out.1.val + 2^64 * out.2.toNat = lhs.val + rhs.val + carry.toNat ⦄ := by
  unfold carry_add
  exact carrying_add_spec lhs rhs carry

@[step]
theorem wide_mul_spec (lhs rhs : U64) :
    wide_mul lhs rhs ⦃ out =>
      out.1.val = (lhs.val * rhs.val) % 2^64 ∧
      out.2.val = (lhs.val * rhs.val) / 2^64 ⦄ := by
  have hlhs : lhs.val % 2^128 = lhs.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hrhs : rhs.val % 2^128 = rhs.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hproduct : lhs.val * rhs.val ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by scalar_tac) (by scalar_tac)
  have hbound : lhs.val * rhs.val < 2^128 := by scalar_tac
  unfold wide_mul
  step*
  all_goals simp_all only [UScalar.cast_val_eq, UScalarTy.numBits,
    Nat.shiftRight_eq_div_pow]
  all_goals scalar_tac

#print axioms overflowing_add_identity
#print axioms overflowing_sub_identity
#print axioms bool_or_disjoint
#print axioms bool_bound
#print axioms carrying_add_flags_disjoint
#print axioms borrowing_sub_flags_disjoint
#print axioms carrying_add_spec
#print axioms borrowing_sub_spec
#print axioms carry_add_spec
#print axioms wide_mul_spec

end CommonVerify
