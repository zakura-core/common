import Common
import Mathlib.Data.Nat.Digits.Defs

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

/-- The ordinary integer of a little-endian byte sequence. -/
def byteValue (bytes : List U8) : Nat :=
  Nat.ofDigits 256 (bytes.map (fun byte => byte.val))

theorem bitvec_from_le_cons (byte : BitVec 8) (bytes : List (BitVec 8)) :
    (BitVec.fromLEBytes (byte :: bytes)).toNat =
      byte.toNat + 256 * (BitVec.fromLEBytes bytes).toNat := by
  rw [BitVec.fromLEBytes]
  simp only [List.length_cons, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  have hb : byte.toNat < 2 ^ (8 * (bytes.length + 1)) :=
    BitVec.toNat_lt_twoPow_of_le (by omega)
  have ht : (BitVec.fromLEBytes bytes).toNat < 2 ^ (8 * (bytes.length + 1)) :=
    BitVec.toNat_lt_twoPow_of_le (by omega)
  have hs : (BitVec.fromLEBytes bytes).toNat * 2 ^ 8 < 2 ^ (8 * (bytes.length + 1)) := by
    have hsmall := (BitVec.fromLEBytes bytes).isLt
    rw [show 8 * (bytes.length + 1) = 8 * bytes.length + 8 by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hsmall (by norm_num)
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hs]
  have hbyte := byte.isLt
  norm_num at hbyte ⊢
  rw [Nat.or_comm]
  simpa only [show (2 : Nat) ^ 8 = 256 by norm_num, Nat.mul_comm, Nat.add_comm] using
    (Nat.two_pow_add_eq_or_of_lt (i := 8) hbyte (BitVec.fromLEBytes bytes).toNat).symm

theorem bitvec_from_le_value (bytes : List U8) :
    (BitVec.fromLEBytes (bytes.map U8.bv)).toNat = byteValue bytes := by
  induction bytes with
  | nil => simp [byteValue, BitVec.fromLEBytes, Nat.ofDigits]
  | cons byte bytes ih =>
      simp only [List.map_cons]
      rw [bitvec_from_le_cons, ih]
      simp [byteValue, Nat.ofDigits]

theorem u64_from_le_value (bytes : Array U8 8#usize) :
    (core.num.U64.from_le_bytes bytes).val = byteValue bytes.val := by
  simp only [core.num.U64.from_le_bytes, UScalar.val, BitVec.toNat_cast]
  exact bitvec_from_le_value _

theorem byte_digits_bound (bytes : List U8) :
    ∀ digit ∈ bytes.map (fun byte => byte.val), digit < 256 := by
  intro digit hdigit
  obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hdigit
  scalar_tac

theorem byteValue_lt (bytes : List U8) : byteValue bytes < 256 ^ bytes.length := by
  unfold byteValue
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 256) (byte_digits_bound bytes)
  simpa only [List.length_map] using h

theorem byteValue_injective (a b : List U8) (hlen : a.length = b.length)
    (hvalue : byteValue a = byteValue b) : a = b := by
  have hmaps := Nat.ofDigits_inj_of_len_eq (by decide : 1 < 256)
    (by simpa only [List.length_map] using hlen) (byte_digits_bound a) (byte_digits_bound b) hvalue
  exact (List.map_inj_right (fun x y h => UScalar.eq_of_val_eq h)).mp hmaps

end UdonVerify.Native
