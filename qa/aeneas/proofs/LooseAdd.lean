import Parameters
import ReduceProofs

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem add_twice_modulus_rust_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4)
    (ha : val4 lhs < 2 * val4 params.modulus)
    (hb : val4 rhs < 2 * val4 params.modulus) :
    add_twice_modulus_rust inst lhs rhs ⦃ out =>
      val4 out = (val4 lhs + val4 rhs) % (2 * val4 params.modulus) ∧
      val4 out < 2 * val4 params.modulus ⦄ := by
  unfold add_twice_modulus_rust
  step -grind with slice_carry_add_limbs_spec as ⟨sumPair, hsum⟩
  rcases sumPair with ⟨sum, carry⟩
  try dsimp only
  rw [params.twice_ok]
  simp only [bind_ok]
  step -grind with slice_borrow_sub_limbs_spec as ⟨reduced, borrow, hsub⟩
  rw [params.twice_val] at hsub
  have hsumlt := val4_lt sum
  have houtlt := val4_lt reduced
  have hthrice := params.thrice_lt
  cases carry <;> cases borrow <;>
    simp only [Bool.toNat_true, Bool.toNat_false, mul_zero, mul_one, add_zero,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true] at hsum hsub ⊢
  · simp only [WP.spec_ok]
    have hdiff : val4 lhs + val4 rhs = val4 reduced + 2 * val4 params.modulus := by omega
    have hlt : val4 reduced < 2 * val4 params.modulus := by omega
    exact ⟨residue_after_sub _ _ _ hdiff hlt, hlt⟩
  · simp only [WP.spec_ok]
    have hlt : val4 sum < 2 * val4 params.modulus := by omega
    exact ⟨by rw [← hsum]; exact (Nat.mod_eq_of_lt hlt).symm, hlt⟩
  · omega
  · simp only [WP.spec_ok]
    have hdiff : val4 lhs + val4 rhs = val4 reduced + 2 * val4 params.modulus := by omega
    have hlt : val4 reduced < 2 * val4 params.modulus := by omega
    exact ⟨residue_after_sub _ _ _ hdiff hlt, hlt⟩

@[step]
theorem add_twice_modulus_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4)
    (ha : val4 lhs < 2 * val4 params.modulus)
    (hb : val4 rhs < 2 * val4 params.modulus) :
    add_twice_modulus inst lhs rhs ⦃ out =>
      val4 out = (val4 lhs + val4 rhs) % (2 * val4 params.modulus) ∧
      val4 out < 2 * val4 params.modulus ⦄ := by
  unfold add_twice_modulus
  exact add_twice_modulus_rust_spec inst params lhs rhs ha hb

#print axioms add_twice_modulus_rust_spec
#print axioms add_twice_modulus_spec
end UdonVerify
