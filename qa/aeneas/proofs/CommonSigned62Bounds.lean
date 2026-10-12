import CommonActiveZeroMath
import CommonCheckCompareMath

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem active62_prefix_bound (a : Signed62) (len : Nat) (hlen : len ≤ 5)
    (hn : ∀ k : Fin 5, k.val < len → 0 ≤ a[k.val]!.val ∧ a[k.val]!.val < signedRadix) :
    0 ≤ active62Value a len ∧ active62Value a len < signedRadix ^ len := by
  induction len with
  | zero => simp [active62Value]
  | succ len ih =>
    have hprevious := ih (by omega) (by intro j hj; exact hn j (by omega))
    have hd := hn ⟨len, by omega⟩ (by dsimp; omega)
    have hp : 0 < signedRadix ^ len := pow_pos (by norm_num [signedRadix]) _
    rw [active62_succ, pow_succ]
    constructor <;> nlinarith

theorem active62_sign_iff (a : Signed62) (len : Nat) (hlen : 1 ≤ len ∧ len ≤ 5)
    (hn : active62Normalized a len) :
    active62Value a len < 0 ↔ a[len - 1]!.val < 0 := by
  have hpref := active62_prefix_bound a (len - 1) (by omega)
    (by intro j hj; exact hn j (by omega))
  have hp : 0 < signedRadix ^ (len - 1) := pow_pos (by norm_num [signedRadix]) _
  have hs := active62_succ a (len - 1)
  rw [show len - 1 + 1 = len from by omega] at hs
  constructor
  · intro h
    by_contra ht
    have hnonneg : 0 ≤ a[len - 1]!.val := by omega
    nlinarith
  · intro ht
    have htop : a[len - 1]!.val ≤ -1 := by omega
    nlinarith

theorem signed62_small_value_bounds (a : Signed62) (hn : signed62Normalized a)
    (hv : -(2 ^ 256) < signed62Value a ∧ signed62Value a < 2 ^ 256) :
    (∀ k : Fin 5, |a[k.val]!.val| ≤ signedRadix) ∧ |a[4]!.val| ≤ 256 := by
  have hpref := active62_low_bound a hn 4 (by decide)
  have hs := active62_succ a 4
  rw [active62_value_five] at hs
  have ht : |a[4]!.val| ≤ 256 := by
    rw [abs_le]
    norm_num only [signedRadix] at hpref hs hv
    constructor <;> omega
  refine ⟨?_, ht⟩
  intro k
  by_cases hk : k.val < 4
  · have hd := hn ⟨k.val, hk⟩
    rw [abs_of_nonneg hd.1]
    exact _root_.le_of_lt hd.2
  · have hk4 : k.val = 4 := by have := k.isLt; omega
    rw [hk4]
    have hb : (256 : Int) ≤ signedRadix := by norm_num [signedRadix]
    exact _root_.le_trans ht hb

#print axioms active62_prefix_bound
#print axioms active62_sign_iff
#print axioms signed62_small_value_bounds
end UdonVerify.CommonSigned62
