import CommonSigned62Base

open Aeneas Std Result

namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

def packed62Digit (limbs : A4) : Nat → Nat
  | 0 => limbs[0]!.val % 2 ^ 62
  | 1 => limbs[0]!.val / 2 ^ 62 + 4 * (limbs[1]!.val % 2 ^ 60)
  | 2 => limbs[1]!.val / 2 ^ 60 + 16 * (limbs[2]!.val % 2 ^ 58)
  | 3 => limbs[2]!.val / 2 ^ 58 + 64 * (limbs[3]!.val % 2 ^ 56)
  | 4 => limbs[3]!.val / 2 ^ 56
  | _ => 0

theorem signed62_join (a b : Nat) (k : Fin 3) (ha : a < 2 ^ 64) :
    ((a / 2 ^ (62 - 2 * k.val)) |||
        ((b * 2 ^ (2 * (k.val + 1))) % 2 ^ 64)) % 2 ^ 62 =
      a / 2 ^ (62 - 2 * k.val) +
        2 ^ (2 * (k.val + 1)) * (b % 2 ^ (60 - 2 * k.val)) := by
  have hlow : a / 2 ^ (62 - 2 * k.val) < 2 ^ (2 * (k.val + 1)) := by
    fin_cases k <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Nat.mul_zero, Nat.sub_zero, Nat.zero_add] at * <;> omega
  have hhigh : (b * 2 ^ (2 * (k.val + 1))) % 2 ^ 64 =
      2 ^ (2 * (k.val + 1)) * (b % 2 ^ (62 - 2 * k.val)) := by
    fin_cases k <;> norm_num at * <;> omega
  rw [hhigh, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hlow]
  fin_cases k <;> norm_num at * <;> omega

theorem packed62_digit_bound (limbs : A4) (k : Fin 5) :
    packed62Digit limbs k.val < 2 ^ 62 := by
  fin_cases k <;> simp only [packed62Digit] <;> norm_num <;> scalar_tac

theorem packed62_value (limbs : A4) :
    packed62Digit limbs 0 + 2 ^ 62 * packed62Digit limbs 1 +
      (2 ^ 62) ^ 2 * packed62Digit limbs 2 + (2 ^ 62) ^ 3 * packed62Digit limbs 3 +
      (2 ^ 62) ^ 4 * packed62Digit limbs 4 = val4 limbs := by
  have h0 := Nat.mod_add_div limbs[0]!.val (2 ^ 62)
  have h1 := Nat.mod_add_div limbs[1]!.val (2 ^ 60)
  have h2 := Nat.mod_add_div limbs[2]!.val (2 ^ 58)
  have h3 := Nat.mod_add_div limbs[3]!.val (2 ^ 56)
  norm_num only [packed62Digit, val4, B] at *
  omega

theorem packed62_top_bound (limbs : A4) (hbound : val4 limbs < 2 ^ 255) :
    packed62Digit limbs 4 < 128 := by
  norm_num only [packed62Digit, val4, B] at *
  omega

theorem packed62_representation (limbs : A4) (out : Signed62)
    (hbound : val4 limbs < 2 ^ 255)
    (hdigits : ∀ k : Fin 5, out[k.val]!.val = (packed62Digit limbs k.val : Int)) :
    signed62Normalized out ∧ signed62Value out = (val4 limbs : Int) ∧
      0 ≤ out[4]!.val ∧ out[4]!.val < 128 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have h := hdigits ⟨k.val, by omega⟩
    rw [h]
    refine ⟨by positivity, ?_⟩
    unfold signedRadix
    exact_mod_cast packed62_digit_bound limbs ⟨k.val, by omega⟩
  · have h := congrArg (fun n : Nat => (n : Int)) (packed62_value limbs)
    unfold signed62Value
    rw [hdigits ⟨0, by decide⟩, hdigits ⟨1, by decide⟩, hdigits ⟨2, by decide⟩,
      hdigits ⟨3, by decide⟩, hdigits ⟨4, by decide⟩]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, signedRadix] using h
  · rw [hdigits ⟨4, by decide⟩]
    positivity
  · rw [hdigits ⟨4, by decide⟩]
    exact_mod_cast packed62_top_bound limbs hbound

#print axioms signed62_join
#print axioms packed62_value
#print axioms packed62_representation

end UdonVerify.CommonSigned62
