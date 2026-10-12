import CommonCoeffWords
import CommonInvHelpers.Funs

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def firstResidueDigit (mu : U64) (row : I128) : I64 :=
  UScalar.hcast .I64 (UScalar.wrapping_mul mu (IScalar.hcast .U64 row) &&& 4611686018427387903#u64)

theorem wrapping_add_word_zero (value : U64) : UScalar.wrapping_add value 0#u64 = value := by
  apply U64.bv_eq_imp_eq
  change value.bv + (0#u64).bv = value.bv
  rw [show (0#u64).bv = 0#64 from by decide, BitVec.add_zero]

theorem first_residue_eq (mu : U64) (row : I128) :
    firstResidueDigit mu row = coeffResidueDigit mu row 0#i64 := by
  unfold firstResidueDigit coeffResidueDigit coeffResidue
  rw [show IScalar.hcast .U64 0#i64 = 0#u64 from by decide, wrapping_add_word_zero]

theorem first_correction_eq (mu : U64) (row : I128) :
    CommonInvHelpers.core.num.I64.wrapping_neg (firstResidueDigit mu row) =
      ok (coeffCorrectWord mu row 0#i64) := by
  unfold CommonInvHelpers.core.num.I64.wrapping_neg coeffCorrectWord
  rw [first_residue_eq]

theorem first_correction_value (mu : U64) (row : I128) :
    (coeffCorrectWord mu row 0#i64).val = -(((mu.val : Int) * row.val) % signedRadix) := by
  have h := (coeff_correct_word_value mu row 0#i64 (by norm_num [signedRadix])).1
  simpa using h

#print axioms wrapping_add_word_zero
#print axioms first_residue_eq
#print axioms first_correction_eq
#print axioms first_correction_value
end UdonVerify.CommonSigned62
