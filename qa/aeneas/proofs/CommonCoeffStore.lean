import CommonCoeffValue
import CommonCoeffRows

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def storeCoeffRow (before : Signed62) (a1 a2 a3 a4 : I128) (tail : I64) : Signed62 :=
  ((((before.set 0#usize (fgRowDigit a1)).set 1#usize (fgRowDigit a2)).set 2#usize
    (fgRowDigit a3)).set 3#usize (fgRowDigit a4)).set 4#usize tail

theorem stored_coeff_row_matches (before : Signed62) (term : Nat → Int)
    (a1 a2 a3 a4 : I128) (tail : I64)
    (h1 : a1.val = fgCarry term 0 + term 1)
    (h2 : a2.val = fgCarry term 1 + term 2)
    (h3 : a3.val = fgCarry term 2 + term 3)
    (h4 : a4.val = fgCarry term 3 + term 4)
    (ht : tail.val = fgCarry term 4) :
    ∀ k : Fin 5, (storeCoeffRow before a1 a2 a3 a4 tail)[k.val]!.val = fgStoredDigit term 5 k.val := by
  intro k
  have hd1 := (fg_row_digit_value a1).1
  have hd2 := (fg_row_digit_value a2).1
  have hd3 := (fg_row_digit_value a3).1
  have hd4 := (fg_row_digit_value a4).1
  fin_cases k <;> simp [storeCoeffRow, Array.getElem!_Nat_set_ne,
    fgStoredDigit, hd1, hd2, hd3, hd4, h1, h2, h3, h4, ht]

#print axioms stored_coeff_row_matches
end UdonVerify.CommonSigned62
