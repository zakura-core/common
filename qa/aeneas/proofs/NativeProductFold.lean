import NativeProductPartial
import NativeProductFoldBridge

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- A lost bit above all nine words is restored modulo the prime. -/
@[step]
theorem product_fold_overflow_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (sum : Sum M) (overflow : U64) (hoverflow : overflow.val ≤ 1) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow inst sum overflow
      ⦃ out => Nat.ModEq (val4 params.modulus) (sumInteger out)
        (sumInteger sum + B ^ 9 * overflow.val) ⦄ := by
  have hcases : overflow = 0#u64 ∨ overflow = 1#u64 := by scalar_tac
  unfold NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow
  rcases hcases with hzero | hone
  · subst overflow
    step -grind
    simp only [show (0#u64) = 0#u64 from rfl, if_pos, WP.spec_ok]
    simpa using Nat.ModEq.refl (sumInteger sum)
  · subst overflow
    step -grind
    simp only [show ¬ ((1#u64) = 0#u64) from by decide, if_false]
    obtain ⟨folded, hpartial, hpartialBound, hpartialRedc, hpartialMod⟩ :=
      WP.spec_imp_exists (product_partial_reduce_spec inst params constants sum)
    rw [hpartial]
    simp only [bind_ok, Std.uncurry]
    rw [constants.conversion.radix2_ok]
    simp only [bind_ok, Std.uncurry]
    have hlimit : val8 folded+B*val4 constants.conversion.radix2<R^2 := by
      have hradix := val4_lt constants.conversion.radix2
      norm_num [B,R] at hpartialBound hradix ⊢
      omega
    with_unfolding_all rw [fold_correction_bind_eq folded constants.conversion.radix2
      (fun final=>ok ({sum with wide:=final,carry:=0#u64} : Sum M))]
    step -grind with (fold_correction_spec folded constants.conversion.radix2 hlimit)
      as ⟨final,hfinal⟩
    try simp only [WP.spec_ok]
    have hr2 : Nat.ModEq (val4 params.modulus) (val4 constants.conversion.radix2)
        (R ^ 2) := by
      simp only [Nat.ModEq, constants.conversion.radix2_val, Nat.mod_mod]
    have hcorrection := hr2.mul_left B
    have hradix : B * R ^ 2 = B ^ 9 := by norm_num [B, R]
    rw [hradix] at hcorrection
    have hmod : Nat.ModEq (val4 params.modulus) (val8 final)
        (sumInteger sum + B ^ 9) := by
      rw [hfinal]
      exact hpartialMod.add hcorrection
    simpa [sumInteger, accumulatorValue] using hmod

#print axioms product_fold_overflow_spec

end UdonVerify.Native
