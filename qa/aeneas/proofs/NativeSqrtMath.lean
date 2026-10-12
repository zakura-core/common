import PastaPrimality
import NativeRootTables
import Mathlib.FieldTheory.Finite.Basic

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem sqrt_initial_power (p exponent n : Nat) (hp : Nat.Prime p)
    (hfactor : (1 + exponent * 2) * 2 ^ n = p - 1)
    (a : ZMod p) (ha : a ≠ 0) :
    (a * (a ^ exponent) ^ 2) ^ (2 ^ n) = 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hbase : a * (a ^ exponent) ^ 2 = a ^ (1 + exponent * 2) := by
    rw [pow_add, pow_one, pow_mul]
  rw [hbase, ← pow_mul, hfactor]
  exact ZMod.pow_card_sub_one_eq_one ha

theorem checked_euler_nonsquare (p value : Nat) (hp : Nat.Prime p)
    (hpLarge : 2 < p) (hpOdd : p % 2 = 1)
    (hexponent : (p - 1) / 2 < 2 ^ 256)
    (hcheck : powMod p value ((p - 1) / 2) = p - 1) :
    ¬ IsSquare (value : ZMod p) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hhalfPositive : 0 < (p - 1) / 2 := by omega
  have hfactor : 2 * ((p - 1) / 2) = p - 1 := by omega
  have hminusZero : ((p - 1 : Nat) : ZMod p) ≠ 0 := by
    intro h
    have hv := (ZMod.natCast_eq_natCast_iff' (p - 1) 0 p).mp
      (by simpa only [Nat.cast_zero] using h)
    rw [Nat.mod_eq_of_lt (by omega : p - 1 < p), Nat.zero_mod] at hv
    omega
  have hchecked : (value : ZMod p) ^ ((p - 1) / 2) = ((p - 1 : Nat) : ZMod p) :=
    powMod_zmod hexponent hcheck
  rintro ⟨x, hx⟩
  have hxNonzero : x ≠ 0 := by
    intro h
    have hvZero : (value : ZMod p) = 0 := by simpa only [h, mul_zero] using hx
    rw [hvZero, zero_pow (by omega : (p - 1) / 2 ≠ 0)] at hchecked
    exact hminusZero hchecked.symm
  have hpower : (value : ZMod p) ^ ((p - 1) / 2) = 1 := by
    rw [hx, ← pow_two, ← pow_mul, hfactor]
    exact ZMod.pow_card_sub_one_eq_one hxNonzero
  have hv := (ZMod.natCast_eq_natCast_iff' (p - 1) 1 p).mp
    (by simpa only [Nat.cast_one] using hchecked.symm.trans hpower)
  rw [Nat.mod_eq_of_lt (by omega : p - 1 < p), Nat.mod_eq_of_lt (by omega : 1 < p)] at hv
  omega

theorem fp_sqrt_nonsquare :
    ¬ IsSquare (rootValue fpPrime fpRadixInverse fpRoots 32 : ZMod fpPrime) := by
  apply checked_euler_nonsquare _ _ fp_prime
  · with_unfolding_all decide
  · with_unfolding_all decide
  · with_unfolding_all decide
  · with_unfolding_all decide

theorem fq_sqrt_nonsquare :
    ¬ IsSquare (rootValue fqPrime fqRadixInverse fqRoots 32 : ZMod fqPrime) := by
  apply checked_euler_nonsquare _ _ fq_prime
  · with_unfolding_all decide
  · with_unfolding_all decide
  · with_unfolding_all decide
  · with_unfolding_all decide

theorem fp_sqrt_initial_power (a : ZMod fpPrime) (ha : a ≠ 0) :
    (a * (a ^ 3369993333393829974333376885877453834209946971612698481878577354870) ^ 2) ^
      (2 ^ 32) = 1 := by
  apply sqrt_initial_power _ _ _ fp_prime
  · with_unfolding_all decide
  · exact ha

theorem fq_sqrt_initial_power (a : ZMod fqPrime) (ha : a ≠ 0) :
    (a * (a ^ 3369993333393829974333376885877453834209946971612708570864021632400) ^ 2) ^
      (2 ^ 32) = 1 := by
  apply sqrt_initial_power _ _ _ fq_prime
  · with_unfolding_all decide
  · exact ha

theorem root_half_power {M : Type} (p inverse : Nat)
    (roots inverseRoots : RootTable M) (hchecks : rootTableChecks p inverse roots inverseRoots)
    (hp : 1 ≤ p) (k : Nat) (hk : 1 ≤ k) (hbound : k ≤ 32) :
    (rootValue p inverse roots k : ZMod p) ^ (2 ^ (k - 1)) = -1 := by
  rcases hchecks ⟨k, by omega⟩ with
    ⟨_, _, _, _, _, hhalf, _, _, _⟩
  have hexponent : 2 ^ (k - 1) < 2 ^ 256 := by
    exact lt_of_le_of_lt (pow_le_pow_right₀ (by decide : 1 ≤ (2 : Nat))
      (by omega : k - 1 ≤ 32)) (by norm_num)
  have h := powMod_zmod hexponent (hhalf hk)
  simpa only [Nat.cast_sub hp, Nat.cast_one, ZMod.natCast_self, zero_sub] using h

theorem root_next_square {M : Type} (p inverse : Nat)
    (roots inverseRoots : RootTable M) (hchecks : rootTableChecks p inverse roots inverseRoots)
    (k : Nat) (hbound : k < 32) :
    (rootValue p inverse roots (k + 1) : ZMod p) ^ 2 = (rootValue p inverse roots k : ZMod p) := by
  rcases hchecks ⟨k, by omega⟩ with
    ⟨_, _, _, _, _, _, hnext, _, _⟩
  have h := congrArg (fun x : Nat => (x : ZMod p)) (hnext hbound)
  simpa only [ZMod.natCast_mod, Nat.cast_pow] using h

#print axioms fp_sqrt_nonsquare
#print axioms fq_sqrt_nonsquare
#print axioms fp_sqrt_initial_power
#print axioms fq_sqrt_initial_power

end UdonVerify.Native
