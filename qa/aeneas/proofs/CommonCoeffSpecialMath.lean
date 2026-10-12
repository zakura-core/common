import CommonCoeffOutput
import CommonCoeffFirstWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def zero62 : Signed62 := Array.repeat 5#usize 0#i64

@[simp] theorem zero62_digit (k : Nat) (hk : k < 5) : zero62[k]! = 0#i64 := by
  have all : ∀ index : Fin 5, zero62[index.val]! = 0#i64 := by
    intro index
    fin_cases index <;> decide
  exact all ⟨k, hk⟩

@[simp] theorem zero62_value : signed62Value zero62 = 0 := by
  norm_num [signed62Value, zero62]

theorem zero62_normalized : signed62Normalized zero62 := by
  intro k
  rw [zero62_digit k.val (by omega)]
  norm_num [signedRadix]

theorem store_coeff_initial_irrelevant (before after : Signed62)
    (a1 a2 a3 a4 : I128) (tail : I64) :
    storeCoeffRow before a1 a2 a3 a4 tail = storeCoeffRow after a1 a2 a3 a4 tail := by
  apply signed62_eq_of_digits
  intro k
  fin_cases k <;> simp [storeCoeffRow, Array.getElem!_Nat_set_ne]

theorem i128_zero_add_eq (value : I128) : (0#i128 + value) = ok value := by
  apply fg_result_eq
  step +scalarTac -grind with I128.add_spec as ⟨out, hout⟩
  apply IScalar.eq_of_val_eq
  simpa using hout

theorem i128_mul_zero_eq (value : I128) : (value * 0#i128) = ok 0#i128 := by
  apply fg_result_eq
  step +scalarTac -grind with I128.mul_spec as ⟨out, hout⟩
  apply IScalar.eq_of_val_eq
  simpa using hout

theorem fg_row_zero_left_eq (u v e : I64) : fgRowTerm u v 0#i64 e = fgZeroTerm v e := by
  unfold fgRowTerm fgZeroTerm
  simp only [lift, bind_ok]
  rw [show core.convert.num.FromI128I64.from 0#i64 = 0#i128 from by decide,
    i128_mul_zero_eq]
  simp only [bind_ok]
  simp only [i128_zero_add_eq]
  exact Std.bind_pure _

theorem coeff_sign_nonnegative_eq (u v d4 e4 : I64)
    (hrow : |u.val| + |v.val| ≤ signedRadix) (hd : 0 ≤ d4.val) (he : 0 ≤ e4.val) :
    coeffSignStart u v d4 e4 = ok 0#i64 := by
  apply fg_result_eq
  apply WP.spec_mono (coeff_sign_start_spec u v d4 e4 hrow)
  intro out hout
  apply IScalar.eq_of_val_eq
  change out.val = 0
  simpa only [if_neg (_root_.not_lt.mpr hd), if_neg (_root_.not_lt.mpr he), zero_add] using hout.1

@[step]
theorem coeff_bounded_add_spec (left right : I128) (a b : Int)
    (hl : |left.val| ≤ a) (hr : |right.val| ≤ b)
    (hfit : a + b ≤ 3 * signedRadix ^ 2 + 3 * signedRadix + 5) :
    left + right ⦃ out => out.val = left.val + right.val ∧ |out.val| ≤ a + b ⦄ := by
  have habs : |left.val + right.val| ≤ a + b := by
    have := abs_add_le left.val right.val
    omega
  have hbounds := coeff_accumulator_i128 (left.val + right.val) (by omega)
  step +scalarTac -grind with I128.add_spec as ⟨out, hout⟩
  exact ⟨hout, by rw [hout]; exact habs⟩

@[step]
theorem first_product_spec (factor digit : I64) (bound : Int)
    (hf : |factor.val| ≤ signedRadix) (hd : |digit.val| ≤ bound)
    (hbound : 0 ≤ bound ∧ bound ≤ signedRadix) :
    fgZeroTerm factor digit ⦃ out => out.val = factor.val * digit.val ∧
      |out.val| ≤ signedRadix * bound ⦄ := by
  have hp : |factor.val * digit.val| ≤ signedRadix * bound := by
    rw [abs_mul]
    nlinarith [abs_nonneg factor.val, abs_nonneg digit.val]
  have hfit := coeff_accumulator_i128 (factor.val * digit.val)
    (by nlinarith only [hp, hbound.2, hbound.1, show (0 : Int) ≤ signedRadix by norm_num [signedRadix]])
  unfold fgZeroTerm
  simp only [lift, bind_ok]
  step +scalarTac -grind with I128.mul_spec as ⟨out, hout⟩
  simp only [core.convert.num.FromI128I64.from_val_eq] at hout
  exact ⟨hout, by rw [hout]; exact hp⟩

#print axioms zero62_digit
#print axioms zero62_value
#print axioms zero62_normalized
#print axioms store_coeff_initial_irrelevant
#print axioms i128_zero_add_eq
#print axioms i128_mul_zero_eq
#print axioms fg_row_zero_left_eq
#print axioms coeff_sign_nonnegative_eq
#print axioms coeff_bounded_add_spec
#print axioms first_product_spec
end UdonVerify.CommonSigned62
