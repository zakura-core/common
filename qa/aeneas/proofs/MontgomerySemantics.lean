import Parameters
import Mathlib.Data.Nat.ModEq

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

theorem certificate_congruence (p t m u : Nat) (h : R*u = t+m*p) :
    Nat.ModEq p (R*u) t := by
  unfold Nat.ModEq
  rw [h]
  simp [Nat.add_mod]

theorem pasta_loose_bound {M : Type}
    {inst : udon_kernel_slice.field.pasta.PrimeModulus M}
    (params : PastaParameters inst) (a b m u : Nat)
    (ha : a < 2 * val4 params.modulus)
    (hb : b < 2 * val4 params.modulus)
    (hm : m < R)
    (hu : R*u = a*b + m*val4 params.modulus) :
    u < 2 * val4 params.modulus := by
  let p := val4 params.modulus
  let c := p - R/4
  have hp : 4 * (p : Int) = (R : Int) + 4 * (c : Int) := by
    have hoff := params.offset_positive
    change R/4 < p at hoff
    have hsub := Nat.sub_add_cancel (Nat.le_of_lt hoff)
    change c + R/4 = p at hsub
    have hquarter : (R / 4 : Nat) * 4 = R := by norm_num [R, B]
    have hsubi : (c : Int) + (R/4 : Nat) = p := by exact_mod_cast hsub
    have hqi : ((R/4 : Nat) : Int) * 4 = (R : Int) := by exact_mod_cast hquarter
    omega
  have hc : (0 : Int) < c := by
    have hoff := params.offset_positive
    dsimp [c, p]
    omega
  have hsmall : 16 * (c : Int)^2 < (R : Int) := by
    exact_mod_cast params.offset_small
  have hae : (a : Int) < 2*(p : Int) := by exact_mod_cast ha
  have hbe : (b : Int) < 2*(p : Int) := by exact_mod_cast hb
  have hme : (m : Int) < (R : Int) := by exact_mod_cast hm
  have hue : (u : Int)*(R : Int) = (a : Int)*(b : Int)+(m : Int)*(p : Int) := by
    rw [Nat.mul_comm R u] at hu
    exact_mod_cast hu
  have h := loose_product_bound p c a b m u hp hc hsmall
    (Int.natCast_nonneg a) hae (Int.natCast_nonneg b) hbe (Int.natCast_nonneg m) hme hue
  exact_mod_cast h

#print axioms pasta_loose_bound

end UdonVerify
