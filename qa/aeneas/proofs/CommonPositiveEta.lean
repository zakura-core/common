import CommonPositiveEtaMath
import CommonDivsteps.Funs
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def positiveCorrection (f : U64) : U64 :=
  UScalar.wrapping_mul (UScalar.wrapping_add f 1#u64 &&& 4#u64) 2#u64

def positiveInverseWord (f : U64) : U64 := UScalar.wrapping_add f (positiveCorrection f)

def positiveEtaWord (f g mask : U64) : U64 :=
  UScalar.wrapping_mul (UScalar.wrapping_sub 0#u64 (positiveInverseWord f)) g &&& mask

theorem wrapping_add_mod_pow (a b : U64) (n : Nat) (hn : n ≤ 64) :
    Int.ModEq (2^n) ((UScalar.wrapping_add a b).val : Int) ((a.val:Int)+b.val) := by
  have h : Nat.ModEq (2^64) (UScalar.wrapping_add a b).val (a.val+b.val) := by
    simp only [UScalar.wrapping_add_val_eq,UScalar.size,UScalarTy.numBits,Nat.ModEq,Nat.mod_mod]
  have hs := h.of_dvd (Nat.pow_dvd_pow 2 hn)
  simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using Int.natCast_modEq_iff.mpr hs

theorem positive_correction_value (f : U64) :
    (positiveCorrection f).val = 8 * (((f.val+1)/4)%2) := by
  unfold positiveCorrection
  rw [UScalar.wrapping_mul_val_eq,UScalar.val_and]
  norm_num only [show (4#u64).val=4 from by decide,show (2#u64).val=2 from by decide]
  rw [and_four_nat,UScalar.wrapping_add_val_eq]
  norm_num only [show (1#u64).val=1 from by decide,UScalar.size,UScalarTy.numBits]
  have hperiod : ((f.val+1)%18446744073709551616)/4%2 = ((f.val+1)/4)%2 := by omega
  rw [hperiod]
  have hsmall : 8 * (((f.val+1)/4)%2) < 18446744073709551616 := by omega
  rw [show 4 * (((f.val+1)/4)%2) * 2 = 8 * (((f.val+1)/4)%2) by omega]
  exact Nat.mod_eq_of_lt hsmall

theorem positive_correction_shift (f : U64) :
    ((core.num.U64.wrapping_add f 1#u64 &&& 4#u64) <<< 1#i32) ⦃ out =>
      out = positiveCorrection f ⦄ := by
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨out,hval,hbv⟩
  apply UScalar.eq_of_val_eq
  rw [hval]
  simp only [positiveCorrection,UScalar.wrapping_mul_val_eq,
    show (2#u64).val=2 from by decide,show (1#i32).toNat=1 from by decide,
    Nat.shiftLeft_eq,U64.size]
  norm_num [core.num.U64.wrapping_add,UScalar.size,U64.size,U64.numBits]

theorem positive_inverse_word_mod (f : U64) :
    Int.ModEq 16 ((positiveInverseWord f).val : Int)
      ((f.val:Int)+8*((((f.val:Int)+1)/4)%2)) := by
  have h := wrapping_add_mod_pow f (positiveCorrection f) 4 (by decide)
  norm_num only at h
  rw [positive_correction_value] at h
  exact_mod_cast h

theorem positive_eta_word_mod (f g mask : U64) (n : Nat) (hn : n ≤ 4)
    (hm : mask.val=2^n-1) :
    Int.ModEq (2^n) ((positiveEtaWord f g mask).val : Int)
      (-((f.val:Int)+8*((((f.val:Int)+1)/4)%2))*g.val) := by
  have hi := (positive_inverse_word_mod f).of_dvd
    (show (2^n:Int) ∣ 16 from by change (2^n:Int) ∣ 2^4;exact pow_dvd_pow 2 hn)
  have hs := wrapping_sub_mod_pow 0#u64 (positiveInverseWord f) n (by omega)
  norm_num only at hs
  have hneg := hs.trans ((Int.ModEq.refl (n:=(2^n)) 0).sub hi)
  have hmul := wrapping_mul_mod_pow (UScalar.wrapping_sub 0#u64 (positiveInverseWord f)) g n (by omega)
  have hmask : Int.ModEq (2^n) ((positiveEtaWord f g mask).val : Int)
      ((UScalar.wrapping_mul (UScalar.wrapping_sub 0#u64 (positiveInverseWord f)) g).val : Int) := by
    unfold positiveEtaWord
    rw [and_mask_mod _ mask n hm]
    simp only [Int.ModEq,Int.natCast_emod,Nat.cast_pow,Nat.cast_ofNat,Int.emod_emod]
  exact hmask.trans (hmul.trans (by simpa only [zero_sub] using hneg.mul_right (g.val:Int)))

theorem positive_eta_word_spec (f g mask : U64) (n : Nat) (hn : n ≤ 4)
    (hm : mask.val=2^n-1) (hodd : f.val%2=1) :
    (positiveEtaWord f g mask).val < 2^n ∧
      (g.val+f.val*(positiveEtaWord f g mask).val)%2^n=0 := by
  constructor
  · unfold positiveEtaWord
    rw [and_mask_mod _ mask n hm]
    exact Nat.mod_lt _ (by positivity)
  · have hword := positive_eta_word_mod f g mask n hn hm
    have hoddInt : (f.val:Int)%2=1 := by exact_mod_cast hodd
    have hcancel := (positive_cancel16 (f.val:Int) g.val hoddInt).of_dvd
      (show (2^n:Int) ∣ 16 from by change (2^n:Int) ∣ 2^4;exact pow_dvd_pow 2 hn)
    have h := (hword.mul_left (f.val:Int)).add_left (g.val:Int)
    have hzero := h.trans hcancel
    change Nat.ModEq (2^n) (g.val+f.val*(positiveEtaWord f g mask).val) 0
    apply Int.natCast_modEq_iff.mp
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_zero] using hzero

#print axioms positive_correction_value
#print axioms positive_correction_shift
#print axioms positive_inverse_word_mod
#print axioms positive_eta_word_spec
end UdonVerify.CommonSigned62
