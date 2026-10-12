import CommonSigned62Packing
import CommonFG62.Funs
import Mathlib.Algebra.Order.Ring.Abs
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem row_term_bound (u v fi gi : Int)
    (huv : |u|+|v| ≤ signedRadix) (hf : |fi| ≤ signedRadix) (hg : |gi| ≤ signedRadix) :
    |u*fi+v*gi| ≤ signedRadix^2 := by
  have hp : 0 ≤ signedRadix := by norm_num [signedRadix]
  have hleft := mul_le_mul_of_nonneg_left hf (abs_nonneg u)
  have hright := mul_le_mul_of_nonneg_left hg (abs_nonneg v)
  have hsum := abs_add_le (u*fi) (v*gi)
  rw [abs_mul,abs_mul] at hsum
  nlinarith [abs_nonneg u,abs_nonneg v]

theorem row_accumulator_bound (carry term : Int)
    (hc : |carry| ≤ signedRadix+2) (ht : |term| ≤ signedRadix^2) :
    |carry+term| ≤ signedRadix^2+signedRadix+2 := by
  have h := abs_add_le carry term
  linarith

theorem row_accumulator_i128 (value : Int)
    (h : |value| ≤ signedRadix^2+signedRadix+2) :
    -(2^127) ≤ value ∧ value < 2^127 := by
  have h0 := neg_le_of_abs_le h
  have h1 := le_of_abs_le h
  norm_num [signedRadix] at h0 h1
  constructor <;> norm_num <;> omega

theorem row_carry_bound (value : Int)
    (h : |value| ≤ signedRadix^2+signedRadix+2) :
    |value/signedRadix| ≤ signedRadix+2 := by
  have h0 := neg_le_of_abs_le h
  have h1 := le_of_abs_le h
  rw [abs_le]
  norm_num [signedRadix] at h0 h1 ⊢
  omega

theorem row_carry_i64 (carry : Int) (h : |carry| ≤ signedRadix+2) :
    -(2^63) ≤ carry ∧ carry < 2^63 := by
  have h0 := neg_le_of_abs_le h
  have h1 := le_of_abs_le h
  norm_num [signedRadix] at h0 h1
  constructor <;> norm_num <;> omega

theorem row_digit_normalized (value : Int) :
    0 ≤ value%signedRadix ∧ value%signedRadix<signedRadix := by
  exact ⟨Int.emod_nonneg value (by norm_num [signedRadix]),
    Int.emod_lt_of_pos value (by norm_num [signedRadix])⟩

theorem row_radix_split (value : Int) :
    value%signedRadix+signedRadix*(value/signedRadix)=value := by
  exact Int.emod_add_mul_ediv value signedRadix

#print axioms row_term_bound
#print axioms row_accumulator_i128
#print axioms row_carry_bound
#print axioms row_carry_i64
#print axioms row_radix_split
end UdonVerify.CommonSigned62
