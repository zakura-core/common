import Parameters
import Mathlib.Data.Nat.ModEq

open Aeneas Std Result
open udon_kernel_slice.field.pasta
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev flagFullMask : U64 := 18446744073709551615#u64

theorem flag_and_zero (x : U64) : x &&& (0#u64) = 0#u64 := by
  apply UScalar.eq_of_val_eq
  change x.val &&& 0 = 0
  exact Nat.and_zero x.val

theorem flag_and_full (x : U64) : x &&& flagFullMask = x := by
  apply UScalar.eq_of_val_eq
  change x.val &&& (2^64-1) = x.val
  rw [Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  scalar_tac

@[step]
theorem wrapping_neg_bool_spec (flag : Bool) :
    udon_kernel_slice.core.num.U64.wrapping_neg (UScalar.cast_fromBool .U64 flag)
      ⦃ out => out = if flag then flagFullMask else 0#u64 ⦄ := by
  cases flag
  · change ok (0#u64) ⦃ out => out = 0#u64 ⦄
    simp only [WP.spec_ok]
  · change ok flagFullMask ⦃ out => out = flagFullMask ⦄
    simp only [WP.spec_ok]

@[step]
theorem sub_twice_modulus_rust_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4)
    (ha : val4 lhs < 2*val4 params.modulus)
    (hb : val4 rhs < 2*val4 params.modulus) :
    sub_twice_modulus_rust inst lhs rhs ⦃ out =>
      val4 out < 2*val4 params.modulus ∧
      Nat.ModEq (2*val4 params.modulus) (val4 out+val4 rhs) (val4 lhs) ⦄ := by
  unfold sub_twice_modulus_rust
  step -grind with slice_borrow_sub_limbs_spec as ⟨difference,borrow,hsub⟩
  simp only [lift,bind_ok]
  step -grind with wrapping_neg_bool_spec as ⟨mask,hmask⟩
  rw [params.twice_ok]
  simp only [bind_ok]
  step -grind with Array.index_usize_spec as ⟨m0,hm0⟩
  step -grind with Array.index_usize_spec as ⟨m1,hm1⟩
  step -grind with Array.index_usize_spec as ⟨m2,hm2⟩
  step -grind with Array.index_usize_spec as ⟨m3,hm3⟩
  have hmasked : val4 (Array.make 4#usize [m0 &&& mask,m1 &&& mask,m2 &&& mask,m3 &&& mask]) =
      2*val4 params.modulus*borrow.toNat := by
    cases borrow
    · simp only [Bool.toNat_false,mul_zero,if_false] at hmask ⊢
      subst mask
      simp_all [val4,flag_and_zero]
    · simp only [Bool.toNat_true,mul_one,if_true] at hmask ⊢
      subst mask
      simpa [val4,flag_and_full,hm0,hm1,hm2,hm3] using params.twice_val
  step -grind with slice_carry_add_limbs_spec as ⟨sum,carry,hsum⟩
  rw [hmasked] at hsum
  have hdifference := val4_lt difference
  have hsumlt := val4_lt sum
  have hcert : val4 sum+val4 rhs = val4 lhs+2*val4 params.modulus*borrow.toNat := by
    have hcarry : carry = borrow := by
      cases carry <;> cases borrow <;>
        simp only [Bool.toNat_false,Bool.toNat_true,mul_zero,mul_one,add_zero] at * <;>
        norm_num only [R,B] at * <;> omega
    rw [hcarry] at hsum
    omega
  have hbound : val4 sum < 2*val4 params.modulus := by
    cases borrow <;>
      simp only [Bool.toNat_false,Bool.toNat_true,mul_zero,mul_one,add_zero] at hcert hsub <;> omega
  try simp only [WP.spec_ok]
  refine ⟨hbound,?_⟩
  unfold Nat.ModEq
  rw [hcert]
  simp [Nat.add_mod,Nat.mul_mod]

@[step]
theorem sub_twice_modulus_spec {M : Type} (inst : PrimeModulus M)
    (params : PastaParameters inst) (lhs rhs : A4)
    (ha : val4 lhs < 2*val4 params.modulus)
    (hb : val4 rhs < 2*val4 params.modulus) :
    sub_twice_modulus inst lhs rhs ⦃ out =>
      val4 out < 2*val4 params.modulus ∧
      Nat.ModEq (2*val4 params.modulus) (val4 out+val4 rhs) (val4 lhs) ⦄ := by
  unfold sub_twice_modulus
  exact sub_twice_modulus_rust_spec inst params lhs rhs ha hb

#print axioms sub_twice_modulus_rust_spec
#print axioms sub_twice_modulus_spec
end UdonVerify
