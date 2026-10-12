import CommonSigned62Bounds
import CommonFG62Value

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem active62_digit_bounds_from_value (a : Signed62) (len : Nat)
    (hlen : 1 ≤ len ∧ len ≤ 5) (hn : active62Normalized a len)
    (hv : |active62Value a len| ≤ signedRadix ^ len) : fgInputsBounded len a := by
  let p := signedRadix ^ (len - 1)
  have hp : 0 < p := pow_pos (by norm_num [signedRadix]) _
  have hprefix := active62_prefix_bound a (len - 1) (by omega)
    (by intro k hk; exact hn k (by omega))
  have hsum := active62_succ a (len - 1)
  rw [show len - 1 + 1 = len from by omega] at hsum
  have hpower : signedRadix ^ len = p * signedRadix := by
    rw [show len = len - 1 + 1 from by omega, pow_succ]
  have hvalue := abs_le.mp hv
  rw [hpower] at hvalue
  have htop : |a[len - 1]!.val| ≤ signedRadix := by
    rw [abs_le]
    constructor
    · by_contra h
      have ht : a[len - 1]!.val ≤ -signedRadix - 1 := by omega
      have hprefixHi : active62Value a (len - 1) < p := hprefix.2
      change active62Value a len = active62Value a (len - 1) + p * a[len - 1]!.val at hsum
      nlinarith only [ht, hp, hprefixHi, hsum, hvalue.1]
    · by_contra h
      have ht : signedRadix + 1 ≤ a[len - 1]!.val := by omega
      change active62Value a len = active62Value a (len - 1) + p * a[len - 1]!.val at hsum
      nlinarith only [ht, hp, hprefix.1, hsum, hvalue.2]
  intro k hk
  by_cases hlow : k.val + 1 < len
  · have hd := hn k hlow
    rw [abs_of_nonneg hd.1]
    exact _root_.le_of_lt hd.2
  · have heq : k.val = len - 1 := by omega
    rwa [heq]

theorem active62_normalized_value_bound (a : Signed62) (len : Nat)
    (hlen : 1 ≤ len ∧ len ≤ 5) (hn : active62Normalized a len)
    (htop : a[len - 1]! = 0#i64 ∨ a[len - 1]! = (-1)#i64) :
    |active62Value a len| ≤ signedRadix ^ (len - 1) := by
  have hprefix := active62_prefix_bound a (len - 1) (by omega)
    (by intro k hk; exact hn k (by omega))
  have hsum := active62_succ a (len - 1)
  rw [show len - 1 + 1 = len from by omega] at hsum
  have hp : 0 < signedRadix ^ (len - 1) := pow_pos (by norm_num [signedRadix]) _
  rw [abs_le, hsum]
  rcases htop with htop | htop
  · rw [htop, show (0#i64).val = 0 from by decide, mul_zero, add_zero]
    constructor <;> omega
  · rw [htop, show ((-1)#i64).val = -1 from by decide, mul_neg_one]
    constructor <;> omega

#print axioms active62_digit_bounds_from_value
#print axioms active62_normalized_value_bound
end UdonVerify.CommonSigned62
