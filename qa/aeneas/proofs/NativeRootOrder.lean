import NativeRootTables
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem checked_power_two_primitive (p value k : Nat) (hp : 2 < p) (hk : k ≤ 32)
    (hpower : powMod p value (2 ^ k) = 1)
    (hhalf : 0 < k → powMod p value (2 ^ (k - 1)) = p - 1) :
    IsPrimitiveRoot (value : ZMod p) (2 ^ k) := by
  letI : NeZero p := ⟨by omega⟩
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hlarge : (2 : Nat) ^ k < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hk) (by norm_num)
  have hfull : (value : ZMod p) ^ (2 ^ k) = 1 := by
    simpa only [Nat.cast_one] using powMod_zmod hlarge hpower
  have horder : orderOf (value : ZMod p) = 2 ^ k := by
    by_cases hz : k = 0
    · subst k
      have heq : (value : ZMod p) = 1 := by simpa only [pow_zero, pow_one] using hfull
      simp only [heq, orderOf_one, pow_zero]
    · have hpositive : 0 < k := by omega
      have hlargeHalf : (2 : Nat) ^ (k - 1) < 2 ^ 256 :=
        lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega : k - 1 ≤ 32)) (by norm_num)
      have hnot : (value : ZMod p) ^ (2 ^ (k - 1)) ≠ 1 := by
        have hz : (value : ZMod p) ^ (2 ^ (k - 1)) = ((p - 1 : Nat) : ZMod p) :=
          powMod_zmod hlargeHalf (hhalf hpositive)
        intro h
        have hv := (ZMod.natCast_eq_natCast_iff' (p - 1) 1 p).mp
          (by simpa only [Nat.cast_one] using hz.symm.trans h)
        have hlow : p - 1 < p := by omega
        have hone : 1 < p := by omega
        simp only [Nat.mod_eq_of_lt hlow,
          Nat.mod_eq_of_lt hone] at hv
        omega
      have hsuccessor : k - 1 + 1 = k := by omega
      have hfull' : (value : ZMod p) ^ (2 ^ (k - 1 + 1)) = 1 := by
        simpa only [hsuccessor] using hfull
      simpa only [hsuccessor] using orderOf_eq_prime_pow (p := 2) hnot hfull'
  simpa only [horder] using IsPrimitiveRoot.orderOf (value : ZMod p)

theorem fp_root_table_primitive (k : Fin 33) :
    IsPrimitiveRoot (rootValue fpPrime fpRadixInverse fpRoots k : ZMod fpPrime)
      (2 ^ k.val) := by
  have hc := fp_root_table_checks k
  exact checked_power_two_primitive _ _ _ (by with_unfolding_all decide) (by omega)
    hc.2.2.2.2.1 hc.2.2.2.2.2.1

theorem fq_root_table_primitive (k : Fin 33) :
    IsPrimitiveRoot (rootValue fqPrime fqRadixInverse fqRoots k : ZMod fqPrime)
      (2 ^ k.val) := by
  have hc := fq_root_table_checks k
  exact checked_power_two_primitive _ _ _ (by with_unfolding_all decide) (by omega)
    hc.2.2.2.2.1 hc.2.2.2.2.2.1

#print axioms fp_root_table_primitive
#print axioms fq_root_table_primitive

theorem fp_inverse_root_table_primitive (k : Fin 33) :
    IsPrimitiveRoot (rootValue fpPrime fpRadixInverse fpInverseRoots k : ZMod fpPrime)
      (2 ^ k.val) := by
  have hc := fp_root_table_checks k
  exact checked_power_two_primitive _ _ _ (by with_unfolding_all decide) (by omega)
    hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2

theorem fq_inverse_root_table_primitive (k : Fin 33) :
    IsPrimitiveRoot (rootValue fqPrime fqRadixInverse fqInverseRoots k : ZMod fqPrime)
      (2 ^ k.val) := by
  have hc := fq_root_table_checks k
  exact checked_power_two_primitive _ _ _ (by with_unfolding_all decide) (by omega)
    hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2

#print axioms fp_inverse_root_table_primitive
#print axioms fq_inverse_root_table_primitive

end UdonVerify.Native
