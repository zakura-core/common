import CommonCombaWords

open Aeneas Std Result

namespace UdonVerify.CommonComba
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem batch_column_add_spec (column : BatchColumn) (lhs rhs : U64)
    (hbound : batchColumnInteger column + lhs.val * rhs.val < B ^ 3) :
    CommonComba.field.pasta.products.add_product column lhs rhs ⦃ out =>
      batchColumnInteger out = batchColumnInteger column + lhs.val * rhs.val ⦄ := by
  have hlhs : lhs.val % 2 ^ 128 = lhs.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hrhs : rhs.val % 2 ^ 128 = rhs.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hproduct : lhs.val * rhs.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by scalar_tac) (by scalar_tac)
  unfold CommonComba.field.pasta.products.add_product
  step*
  all_goals simp_all only [UScalar.cast_val_eq, UScalar.cast_fromBool_val_eq, UScalarTy.numBits,
    Nat.shiftRight_eq_div_pow, hlhs, hrhs]
  all_goals simp_all [batchColumnInteger, Array.make, B]
  all_goals
    have hquotient : lhs.val * rhs.val / (2 ^ 64) < 2 ^ 64 := by omega
    try simp_all only [Nat.mod_eq_of_lt hquotient]
    split_ifs at * <;> simp_all [U64.max, U64.size, U64.numBits, UScalarTy.numBits]
    <;> scalar_tac

#print axioms batch_column_add_spec

end UdonVerify.CommonComba
