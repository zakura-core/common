import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

namespace UdonVerify

/-- Repeated squaring with reduction at every multiplication. -/
def powModAux (bits modulus base exponent : Nat) : Nat :=
  match bits with
  | 0 => 1 % modulus
  | bits + 1 =>
    if exponent = 0 then 1 % modulus else
      let half := powModAux bits modulus base (exponent / 2)
      (half * half * (if exponent % 2 = 0 then 1 else base)) % modulus

theorem powModAux_zmod (bits modulus base exponent : Nat)
    (he : exponent < 2 ^ bits) :
    (powModAux bits modulus base exponent : ZMod modulus) =
      (base : ZMod modulus) ^ exponent := by
  induction bits generalizing exponent with
  | zero =>
      have hz : exponent = 0 := by simpa using he
      simp [powModAux, hz, ZMod.natCast_mod]
  | succ bits ih =>
      simp only [powModAux]
      split
      · rename_i hz
        simp [hz, ZMod.natCast_mod]
      · have hh : exponent / 2 < 2 ^ bits := by
          rw [pow_succ] at he
          omega
        simp only [ZMod.natCast_mod, Nat.cast_mul]
        rw [ih _ hh]
        have hsplit : exponent = (exponent / 2) * 2 + exponent % 2 := by omega
        by_cases heven : exponent % 2 = 0
        · simp only [heven, ↓reduceIte, Nat.cast_one, mul_one]
          conv_rhs => rw [hsplit]
          simp [heven, pow_mul, pow_two]
        · have hodd : exponent % 2 = 1 := by omega
          simp only [heven, ↓reduceIte]
          conv_rhs => rw [hsplit]
          simp [hodd, pow_add, pow_mul, pow_two]

/-- A bounded evaluator for all exponents in the Pasta certificates. -/
def powMod (modulus base exponent : Nat) : Nat :=
  powModAux 256 modulus base exponent

theorem powMod_zmod {modulus base exponent residue : Nat}
    (he : exponent < 2 ^ 256)
    (h : powMod modulus base exponent = residue) :
    (base : ZMod modulus) ^ exponent = (residue : ZMod modulus) := by
  have hc := powModAux_zmod 256 modulus base exponent he
  change (powMod modulus base exponent : ZMod modulus) = _ at hc
  rw [h] at hc
  exact hc.symm

theorem prime_mem_of_dvd_product {q : Nat} (hq : q.Prime) (factors : List Nat)
    (hprime : ∀ r ∈ factors, r.Prime) (hdiv : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil =>
      simpa using hq.not_dvd_one hdiv
  | cons r rs ih =>
      rw [List.prod_cons] at hdiv
      rcases hq.dvd_mul.mp hdiv with hr | hrs
      · have heq := (Nat.prime_dvd_prime_iff_eq hq (hprime r (by simp))).mp hr
        simp [heq]
      · exact List.mem_cons_of_mem r (ih (fun s hs => hprime s (by simp [hs])) hrs)

theorem lucas_list_prime (n a : Nat) (factors : List Nat)
    (hfactor : n - 1 = factors.prod)
    (hprime : ∀ q ∈ factors, q.Prime)
    (hpower : (a : ZMod n) ^ (n - 1) = 1)
    (hproper : ∀ q ∈ factors, (a : ZMod n) ^ ((n - 1) / q) ≠ 1) : n.Prime := by
  apply lucas_primality n (a : ZMod n) hpower
  intro q hq hdiv
  rw [hfactor] at hdiv
  exact hproper q (prime_mem_of_dvd_product hq factors hprime hdiv)

end UdonVerify
