import CommonCancellationWords
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem positive_inverse16 (f : Int) (hodd : f % 2 = 1) :
    Int.ModEq 16 (f * (f + 8 * (((f+1)/4)%2))) 1 := by
  have hsmall : 0 ≤ f%16 ∧ f%16 < 16 :=
    ⟨Int.emod_nonneg f (by decide),Int.emod_lt_of_pos f (by decide)⟩
  have hparity : (f%16)%2 = 1 := by omega
  have hperiod : ((f+1)/4)%2 = (((f%16)+1)/4)%2 := by omega
  have hcases : f%16=1 ∨ f%16=3 ∨ f%16=5 ∨ f%16=7 ∨
    f%16=9 ∨ f%16=11 ∨ f%16=13 ∨ f%16=15 := by omega
  rcases hcases with h|h|h|h|h|h|h|h <;>
    norm_num [Int.ModEq,Int.mul_emod,Int.add_emod,hperiod,h]

theorem positive_cancel16 (f g : Int) (hodd : f % 2 = 1) :
    Int.ModEq 16 (g + f * (-(f + 8 * (((f+1)/4)%2)) * g)) 0 := by
  have h := (positive_inverse16 f hodd).mul_right (-g)
  have hz := h.add_left g
  convert hz using 1 <;> ring

theorem and_four_nat (value : Nat) :
    value &&& 4 = 4 * ((value/4)%2) := by
  rw [Nat.and_comm]
  have h := Nat.two_pow_and value 2
  norm_num only at h
  rw [h]
  congr 1
  simpa only [show (2^2:Nat)=4 from by decide] using Nat.toNat_testBit value 2

#print axioms positive_inverse16
#print axioms positive_cancel16
#print axioms and_four_nat
end UdonVerify.CommonSigned62
