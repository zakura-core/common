import CommonDivstepCancel
import NativeSigned

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def addMulWord (g f w : U64) : U64 :=
  UScalar.wrapping_add g (UScalar.wrapping_mul f w)

def rowWord (u v f0 g0 : U64) : U64 :=
  UScalar.wrapping_add (UScalar.wrapping_mul u f0) (UScalar.wrapping_mul v g0)

theorem word_eq_of_mod (a b : U64)
    (h : Int.ModEq (2 ^ 64) (a.val : Int) (b.val : Int)) : a = b := by
  apply UScalar.eq_of_val_eq
  have ha : a.val < 2 ^ 64 := by scalar_tac
  have hb : b.val < 2 ^ 64 := by scalar_tac
  have hn : Nat.ModEq (2 ^ 64) a.val b.val := Int.natCast_modEq_iff.mp h
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hn

theorem word_shift_bv_mod (value shifted : U64) (count : Nat)
    (h : shifted.bv = value.bv <<< count) :
    Int.ModEq (2 ^ 64) (shifted.val : Int) ((value.val : Int) * 2 ^ count) := by
  have hn : Nat.ModEq (2 ^ 64) shifted.val (value.val * 2 ^ count) := by
    simp only [Nat.ModEq, UScalar.val, h, BitVec.toNat_shiftLeft, UScalarTy.numBits,
      Nat.shiftLeft_eq, Nat.mod_mod]
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using Int.natCast_modEq_iff.mpr hn

theorem word_signed_value (word : U64) (value : Int) (hvalue : |value| ≤ signedRadix)
    (h : Int.ModEq (2 ^ 64) (word.val : Int) value) :
    (UScalar.hcast .I64 word).val = value := by
  have hc : Int.ModEq (2 ^ 64) (UScalar.hcast .I64 word).val (word.val : Int) := by
    have hb := Int.bmod_emod (x := (word.val : Int)) (m := (18446744073709551616 : Nat))
    norm_num only at hb
    norm_num only [Int.ModEq, UScalar.hcast_val_eq, IScalarTy.numBits]
    exact hb
  have hm := hc.trans h
  have hmin := (UScalar.hcast .I64 word).hmin
  have hmax := (UScalar.hcast .I64 word).hmax
  norm_num only [IScalar.cMin, IScalar.cMax, IScalarTy.numBits] at hmin hmax
  have hv := abs_le.mp hvalue
  norm_num only [signedRadix, Int.ModEq] at hv hm
  omega

theorem modEq_mul_pow (bits count : Nat) (a b : Int)
    (h : Int.ModEq (2 ^ bits) a b) :
    Int.ModEq (2 ^ (bits + count)) (a * 2 ^ count) (b * 2 ^ count) := by
  simpa only [pow_add] using h.mul_right' (c := (2 ^ count : Int))

theorem modEq_div_pow (bits count : Nat) (a b : Int)
    (h : Int.ModEq (2 ^ (count + bits)) a b)
    (ha : (2 ^ count : Int) ∣ a) (hb : (2 ^ count : Int) ∣ b) :
    Int.ModEq (2 ^ bits) (a / 2 ^ count) (b / 2 ^ count) := by
  have htwice : Int.ModEq ((2 ^ count : Int) * 2 ^ bits)
      (2 ^ count * (a / 2 ^ count)) (2 ^ count * (b / 2 ^ count)) := by
    rw [Int.mul_ediv_cancel' ha, Int.mul_ediv_cancel' hb]
    simpa only [pow_add] using h
  exact Int.ModEq.mul_left_cancel' (by positivity : (2 ^ count : Int) ≠ 0) htwice

theorem row_word_mod (u v f0 g0 : U64) (left right : Int)
    (hu : Int.ModEq (2 ^ 64) (u.val : Int) left)
    (hv : Int.ModEq (2 ^ 64) (v.val : Int) right) :
    Int.ModEq (2 ^ 64) ((rowWord u v f0 g0).val : Int)
      (left * f0.val + right * g0.val) := by
  have hfirst := (wrapping_mul_mod_pow u f0 64 (by decide)).trans (hu.mul_right (f0.val : Int))
  have hsecond := (wrapping_mul_mod_pow v g0 64 (by decide)).trans (hv.mul_right (g0.val : Int))
  exact (wrapping_add_mod_pow (UScalar.wrapping_mul u f0) (UScalar.wrapping_mul v g0)
    64 (by decide)).trans (hfirst.add hsecond)

theorem row_word_shift_eq (u v f0 g0 f shifted : U64) (left right full : Int) (count : Nat)
    (hcount : count ≤ 64)
    (hu : Int.ModEq (2 ^ 64) (u.val : Int) left)
    (hv : Int.ModEq (2 ^ 64) (v.val : Int) right)
    (hf : Int.ModEq (2 ^ (64 - count)) (f.val : Int) full)
    (haction : left * f0.val + right * g0.val = 2 ^ count * full)
    (hshift : shifted.bv = f.bv <<< count) : rowWord u v f0 g0 = shifted := by
  have hrow := row_word_mod u v f0 g0 left right hu hv
  rw [haction] at hrow
  have hsum : 64 - count + count = 64 := by omega
  have hscaled := modEq_mul_pow (64 - count) count (f.val : Int) full hf
  rw [hsum] at hscaled
  have htarget := (word_shift_bv_mod f shifted count hshift).trans hscaled
  apply word_eq_of_mod
  exact hrow.trans (by simpa only [mul_comm] using htarget.symm)

theorem add_mul_word_low_zero (g f w : U64) (n : Nat) (hn : n ≤ 64)
    (hcancel : (g.val + f.val * w.val) % 2 ^ n = 0) :
    (addMulWord g f w).val % 2 ^ n = 0 := by
  have hfull : Nat.ModEq (2 ^ 64) (addMulWord g f w).val (g.val + f.val * w.val) := by
    simp only [Nat.ModEq, addMulWord, UScalar.wrapping_add_val_eq,
      UScalar.wrapping_mul_val_eq, UScalar.size, UScalarTy.numBits, Nat.add_mod, Nat.mod_mod]
  have hlow := hfull.of_dvd (Nat.pow_dvd_pow 2 hn)
  change (addMulWord g f w).val % 2 ^ n = (g.val + f.val * w.val) % 2 ^ n at hlow
  exact hlow.trans hcancel

theorem add_mul_word_mask_zero (g f w mask : U64) (n : Nat) (hn : n ≤ 64)
    (hm : mask.val = 2 ^ n - 1) (hcancel : (g.val + f.val * w.val) % 2 ^ n = 0) :
    addMulWord g f w &&& mask = 0#u64 := by
  apply UScalar.eq_of_val_eq
  change (addMulWord g f w &&& mask).val = 0
  rw [and_mask_mod _ mask n hm]
  exact add_mul_word_low_zero g f w n hn hcancel

theorem sentinel_count_ge_of_low_zero (value : U64) (remaining n : Nat)
    (hr : remaining < 64) (hn : n ≤ remaining) (hzero : value.val % 2 ^ n = 0) :
    n ≤ trailingZeros64 (sentinelWord value remaining) := by
  by_contra h
  have hlt : trailingZeros64 (sentinelWord value remaining) < n := by omega
  have hodd := sentinel_odd_quotient value remaining hr (by omega)
  have hbit := Nat.mod_two_eq_one_iff_testBit_zero.mp hodd
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight] at hbit
  simp only [Nat.add_zero] at hbit
  have hz := congrArg (fun a : Nat => a.testBit (trailingZeros64 (sentinelWord value remaining))) hzero
  simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit, hlt, decide_true, Bool.true_and] at hz
  rw [hbit] at hz
  contradiction

@[step]
theorem native_unsigned_abs_spec (value : I64) :
    CommonDivsteps.core.num.I64.unsigned_abs value ⦃ out => out.val = value.val.natAbs ⦄ := by
  exact UdonVerify.Native.unsigned_abs_spec value

#print axioms word_eq_of_mod
#print axioms word_shift_bv_mod
#print axioms word_signed_value
#print axioms modEq_mul_pow
#print axioms modEq_div_pow
#print axioms row_word_mod
#print axioms row_word_shift_eq
#print axioms add_mul_word_low_zero
#print axioms add_mul_word_mask_zero
#print axioms sentinel_count_ge_of_low_zero
#print axioms native_unsigned_abs_spec
end UdonVerify.CommonSigned62
