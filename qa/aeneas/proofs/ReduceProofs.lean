import Parameters
import SubtractProofs

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem residue_after_sub (x y p : Nat) (h : x = y+p) (hy : y < p) :
    y = x % p := by
  rw [h, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hy]

@[step]
theorem reduce_once_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (limbs : A4)
    (hbound : val4 limbs < 2 * val4 params.modulus) :
    reduce_once inst limbs ⦃ out =>
      val4 out = val4 limbs % val4 params.modulus ∧
      val4 out < val4 params.modulus ⦄ := by
  unfold reduce_once
  rw [params.modulus_ok]
  simp only [bind_ok]
  step with slice_subtract_limbs_spec as ⟨out, borrow, hborrow, hid⟩
  split
  · simp only [WP.spec_ok]
    have hb : borrow.val = 0 := by scalar_tac
    have heq : val4 limbs = val4 out + val4 params.modulus := by
      simp [hb] at hid
      omega
    have hlt : val4 out < val4 params.modulus := by omega
    exact ⟨residue_after_sub _ _ _ heq hlt, hlt⟩
  · simp only [WP.spec_ok]
    have hb : borrow.val = 1 := by scalar_tac
    have hout := val4_lt out
    have hlt : val4 limbs < val4 params.modulus := by
      simp [hb] at hid
      norm_num [R, B] at hid hout
      omega
    exact ⟨(Nat.mod_eq_of_lt hlt).symm, hlt⟩

@[step]
theorem reduce_twice_modulus_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (limbs : A4) (carry : U64)
    (hbound : val4 limbs + R * carry.val < 4 * val4 params.modulus) :
    reduce_twice_modulus inst limbs carry ⦃ out =>
      val4 out = (val4 limbs + R * carry.val) % (2 * val4 params.modulus) ∧
      val4 out < 2 * val4 params.modulus ⦄ := by
  have hthrice := params.thrice_lt
  have hcarry : carry.val ≤ 1 := by
    norm_num [R, B] at hbound hthrice ⊢
    omega
  unfold reduce_twice_modulus
  rw [params.twice_ok]
  simp only [bind_ok]
  step with slice_subtract_limbs_spec as ⟨out, borrow, hborrow, hid⟩
  rw [params.twice_val] at hid
  have hout := val4_lt out
  split
  · simp only [WP.spec_ok]
    have hc : carry.val = 1 := by scalar_tac
    have hb : borrow.val = 1 := by
      norm_num [R, B] at hbound hthrice hid hout
      omega
    have heq : val4 limbs + R * carry.val = val4 out + 2 * val4 params.modulus := by
      simp [hc, hb] at hid ⊢
      omega
    have hlt : val4 out < 2 * val4 params.modulus := by omega
    exact ⟨residue_after_sub _ _ _ heq hlt, hlt⟩
  · have hc : carry.val = 0 := by scalar_tac
    split
    · simp only [WP.spec_ok]
      have hb : borrow.val = 0 := by scalar_tac
      have heq : val4 limbs + R * carry.val = val4 out + 2 * val4 params.modulus := by
        simp [hc, hb] at hid ⊢
        omega
      have hlt : val4 out < 2 * val4 params.modulus := by omega
      exact ⟨residue_after_sub _ _ _ heq hlt, hlt⟩
    · simp only [WP.spec_ok]
      have hb : borrow.val = 1 := by scalar_tac
      have hlt : val4 limbs < 2 * val4 params.modulus := by
        simp [hb] at hid
        norm_num [R, B] at hid hout
        omega
      simp only [hc, mul_zero, add_zero]
      exact ⟨(Nat.mod_eq_of_lt hlt).symm, hlt⟩

#print axioms reduce_once_spec
#print axioms reduce_twice_modulus_spec

end UdonVerify
