import NativeLargeTableChecks
import NativeLongByteMath
import LargeSqrtMath

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 10000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024

def largeWordValue {M : Type} (p inverse : Nat) (table : LargeTable M)
    (digit index : Nat) : ZMod p :=
  (largePowerWord p table digit index : ZMod p) * (inverse : ZMod p)

/-- The checked finite progressions imply the mathematical power at every table index. -/
theorem large_progression_power {M : Type} (p inverse root : Nat) (table : LargeTable M)
    (hchecks : largeProgressionChecks p inverse root table)
    (hinverse : Nat.ModEq p (R * inverse) 1) (digit : Fin 4) (index : Nat)
    (hindex : index < 256) :
    largeWordValue p inverse table digit.val index = (root : ZMod p) ^ (index * 256 ^ digit.val) := by
  have hradix : (R : ZMod p) * (inverse : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff' (R * inverse) 1 p).mpr hinverse
    simpa only [Nat.cast_mul, Nat.cast_one] using h
  have hexponent : 256 ^ digit.val < 2 ^ 256 := by fin_cases digit <;> norm_num
  have hstep : largeWordValue p inverse table digit.val 1 = (root : ZMod p) ^ (256 ^ digit.val) := by
    have h := powMod_zmod hexponent (hchecks digit).2.1.symm
    simpa only [largeWordValue, ZMod.natCast_mod, Nat.cast_mul] using h.symm
  induction index with
  | zero =>
    simp only [largeWordValue, (hchecks digit).1, ZMod.natCast_mod, zero_mul, pow_zero]
    exact hradix
  | succ index ih =>
    have hnext := ((hchecks digit).2.2 ⟨index, by omega⟩).2.2 (by omega : index < 255)
    calc
      largeWordValue p inverse table digit.val (index + 1) =
          largeWordValue p inverse table digit.val index * largeWordValue p inverse table digit.val 1 := by
        simp only [largeWordValue, hnext, ZMod.natCast_mod, Nat.cast_mul]
        ring
      _ = (root : ZMod p) ^ (index * 256 ^ digit.val) * (root : ZMod p) ^ (256 ^ digit.val) := by
        rw [ih (by omega), hstep]
      _ = (root : ZMod p) ^ ((index + 1) * 256 ^ digit.val) := by rw [← pow_add]; congr 1; ring

/-- A canonical stored value is determined by its decoded field value. -/
theorem large_canonical_word_eq (p inverse lhs rhs : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1) (hlhs : lhs < p) (hrhs : rhs < p)
    (hvalue : (lhs : ZMod p) * (inverse : ZMod p) = (rhs : ZMod p) * (inverse : ZMod p)) :
    lhs = rhs := by
  have hdecode : Nat.ModEq p (lhs * inverse) (rhs * inverse) :=
    (ZMod.natCast_eq_natCast_iff' (lhs * inverse) (rhs * inverse) p).mp
      (by simpa only [Nat.cast_mul] using hvalue)
  have hscaled := hdecode.mul_right R
  have hl : Nat.ModEq p ((lhs * inverse) * R) lhs := by
    convert hinverse.mul_left lhs using 1 <;> ring
  have hr : Nat.ModEq p ((rhs * inverse) * R) rhs := by
    convert hinverse.mul_left rhs using 1 <;> ring
  have h := hl.symm.trans (hscaled.trans hr)
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hlhs, Nat.mod_eq_of_lt hrhs] using h

/-- The actual inverse table returns the uniquely required byte for any canonical subgroup input. -/
theorem large_inverse_table_value {M : Type} (p inverse root multiplier : Nat) (table : LargeTable M)
    (hchecks : largeProgressionChecks p inverse root table)
    (hlookup : largeInverseChecks p multiplier table)
    (hinverse : Nat.ModEq p (R * inverse) 1) (hroot : (root : ZMod p) ^ (256 ^ 4) = 1)
    (raw exponent : Nat) (hraw : raw < p) (hexponent : exponent < 256)
    (hvalue : ((raw : ZMod p) * (inverse : ZMod p)) *
      (root : ZMod p) ^ (exponent * 256 ^ 3) = 1) :
    table.inverse[largeHash (raw % 2 ^ 32) multiplier]!.val = exponent := by
  let index : Nat := (256 - exponent) % 256
  have hindex : index < 256 := Nat.mod_lt _ (by decide)
  have hsubgroup := LargeSqrt.subgroup_inverse_value (root : ZMod p)
    ((raw : ZMod p) * (inverse : ZMod p)) hroot exponent hexponent hvalue
  have htable := large_progression_power p inverse root table hchecks hinverse ⟨3, by decide⟩ index hindex
  have htableBound := ((hchecks ⟨3, by decide⟩).2.2 ⟨index, hindex⟩).2.1
  have hword : raw = largePowerWord p table 3 index :=
    large_canonical_word_eq p inverse _ _ hinverse hraw htableBound (hsubgroup.trans htable.symm)
  rw [hword]
  have h := hlookup ⟨index, hindex⟩
  simpa only [index, LargeSqrt.inverse_byte_complement exponent hexponent] using h

#print axioms large_progression_power
#print axioms large_canonical_word_eq
#print axioms large_inverse_table_value

end UdonVerify.Native
