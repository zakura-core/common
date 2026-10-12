import CommonInversionEntry
import NativePredicates
import Mathlib.Data.Nat.Prime.Basic

namespace UdonVerify.PublicInversion
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem canonical_input_is_unit (p x : Nat) (hp : Nat.Prime p) (hx : x < p) (hnz : x ≠ 0) :
    Int.gcd (p : Int) (x : Int) = 1 := by
  rw [Int.gcd_natCast_natCast]
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hnz) hx)

theorem weighted_inverse_decodes (p inverse x y : Nat) (hp : 1 < p)
    (hradix : Nat.ModEq p (R * inverse) 1)
    (hweighted : Int.ModEq (p : Int) ((x : Int) * (y : Int)) (2 ^ 512)) :
    ((x * inverse) % p * ((y * inverse) % p)) % p = 1 := by
  have hn : Nat.ModEq p (x * y) (R ^ 2) := by
    apply Int.natCast_modEq_iff.mp
    norm_num [R, B] at hweighted ⊢
    exact hweighted
  have hleft : Nat.ModEq p ((x * inverse) * (y * inverse)) ((R * inverse) ^ 2) := by
    convert hn.mul_right (inverse ^ 2) using 1 <;> ring
  have hright : Nat.ModEq p ((R * inverse) ^ 2) 1 := by
    simpa only [one_pow] using hradix.pow 2
  have hfinal := hleft.trans hright
  rw [← Nat.mul_mod]
  exact Eq.trans hfinal (Nat.mod_eq_of_lt hp)

#print axioms canonical_input_is_unit
#print axioms weighted_inverse_decodes
end UdonVerify.PublicInversion
