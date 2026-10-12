import CommonSigned62Math
import Mathlib.Data.Int.ModEq
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem odd_square_mod8 (f : Int) (hodd : f%2=1) : (f*f)%8=1 := by
  have hsmall : 0≤f%8 ∧ f%8<8 := ⟨Int.emod_nonneg f (by decide),Int.emod_lt_of_pos f (by decide)⟩
  have hparity : (f%8)%2=1 := by omega
  have hcases : f%8=1 ∨ f%8=3 ∨ f%8=5 ∨ f%8=7 := by omega
  rcases hcases with h|h|h|h <;> norm_num [Int.mul_emod,h]

theorem negative_cancel64 (f g : Int) (hodd : f%2=1) :
    Int.ModEq 64 (g+f*(f*g*(f*f-2))) 0 := by
  have h8 : 8 ∣ f*f-1 := Int.dvd_iff_emod_eq_zero.mpr (by
    rw [Int.sub_emod,odd_square_mod8 f hodd]
    norm_num)
  have h64 : (64:Int) ∣ (f*f-1)^2 := by
    have h := Int.mul_dvd_mul h8 h8
    norm_num only at h
    simpa only [pow_two] using h
  have hscaled : (64:Int) ∣ g*(f*f-1)^2 := dvd_mul_of_dvd_right h64 g
  apply Int.modEq_zero_iff_dvd.mpr
  convert hscaled using 1 <;> ring

#print axioms odd_square_mod8
#print axioms negative_cancel64
end UdonVerify.CommonSigned62
