import CommonCancellationMath
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem wrapping_mul_mod_pow (a b : U64) (n : Nat) (hn : n≤64) :
    Int.ModEq (2^n) ((UScalar.wrapping_mul a b).val : Int) ((a.val:Int)*b.val) := by
  have h : Nat.ModEq (2^64) (UScalar.wrapping_mul a b).val (a.val*b.val) := by
    simp only [UScalar.wrapping_mul_val_eq,UScalar.size,UScalarTy.numBits,Nat.ModEq,Nat.mod_mod]
  have hs := h.of_dvd (Nat.pow_dvd_pow 2 hn)
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using Int.natCast_modEq_iff.mpr hs

theorem wrapping_sub_mod_pow (a b : U64) (n : Nat) (hn : n≤64) :
    Int.ModEq (2^n) ((UScalar.wrapping_sub a b).val : Int) ((a.val:Int)-b.val) := by
  have h : Int.ModEq (2^64) ((UScalar.wrapping_sub a b).val : Int) ((a.val:Int)-b.val) := by
    rw [UScalar.wrapping_sub_val_eq]
    simp only [UScalar.size,UScalarTy.numBits]
    rw [Int.natCast_emod,Nat.cast_add,Nat.cast_sub (by scalar_tac)]
    norm_num only [Nat.cast_pow,Nat.cast_ofNat]
    change ((a.val:Int)+(2^64-b.val))%(2^64)%(2^64)=((a.val:Int)-b.val)%(2^64)
    simp only [Int.emod_emod]
    rw [show (a.val:Int)+(2^64-b.val)=(a.val:Int)-b.val+2^64 by ring]
    simp
  exact h.of_dvd (pow_dvd_pow 2 hn)

theorem and_mask_mod (value mask : U64) (n : Nat) (hm : mask.val=2^n-1) :
    (value &&& mask).val=value.val%2^n := by
  simp only [UScalar.val_and,hm]
  exact Nat.and_two_pow_sub_one_eq_mod value.val n

#print axioms wrapping_mul_mod_pow
#print axioms wrapping_sub_mod_pow
#print axioms and_mask_mod
end UdonVerify.CommonSigned62
