import CommonProductPairsFoldLoops

open Aeneas Std Result

namespace UdonVerify.ProductPairs
open UdonVerify.Native UdonVerify.ProductPortable
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Relate generated tuple binders to ordinary Lean projection binders. -/
theorem pairs_uncurry_projection {A B C : Type} (f : A → B → C) :
    Std.uncurry f = (fun pair => f pair.1 pair.2) := by
  funext pair
  rcases pair with ⟨a,b⟩
  rfl

/-- A lost bit above all nine words is restored modulo the prime. -/
@[step]
theorem pairs_fold_overflow_spec {M : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (sum : ProductPortable.Sum M) (overflow : U64) (hoverflow : overflow.val ≤ 1) :
    CommonProductPairs.field.pasta.products.ProductSum.fold_overflow (portableDict inst) sum overflow
      ⦃ out => Nat.ModEq (val4 params.modulus) (sumInteger out)
        (sumInteger sum + B ^ 9 * overflow.val) ⦄ := by
  have hcases : overflow = 0#u64 ∨ overflow = 1#u64 := by scalar_tac
  unfold CommonProductPairs.field.pasta.products.ProductSum.fold_overflow
  rcases hcases with hzero | hone
  · subst overflow
    step -grind
    simp only [show (0#u64) = 0#u64 from rfl, if_pos, WP.spec_ok]
    simpa using Nat.ModEq.refl (sumInteger sum)
  · subst overflow
    step -grind
    simp only [show ¬ ((1#u64) = 0#u64) from by decide, if_false]
    obtain ⟨folded, hpartial, hpartialBound, hpartialRedc, hpartialMod⟩ :=
      WP.spec_imp_exists (product_partial_reduce_spec inst params constants (sumToNative sum))
    rw [PortableBridge.field.pasta.products.ProductSum.partial_reduce, portable_partial_reduce_bridge, hpartial]
    simp only [bind_ok, Std.uncurry]
    have hr2ok : (portableDict inst).sealedParametersInst.R2 = ok constants.conversion.radix2 :=
      constants.conversion.radix2_ok
    rw [hr2ok]
    simp only [bind_ok, Std.uncurry]
    have hlimit : val8 folded+B*val4 constants.conversion.radix2<R^2 := by
      have hradix := val4_lt constants.conversion.radix2
      norm_num [B,R] at hpartialBound hradix ⊢
      omega
    have hspec : (do
        let final ← pairsFoldCorrection folded constants.conversion.radix2
        ok ({sum with wide:=final,carry:=0#u64} : ProductPortable.Sum M))
        ⦃ out => Nat.ModEq (val4 params.modulus) (ProductPortable.sumInteger out)
          (ProductPortable.sumInteger sum + B^9 * (1#u64).val) ⦄ := by
      step -grind with (pairs_fold_correction_spec folded constants.conversion.radix2 hlimit)
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
      simpa [ProductPortable.sumInteger, sumToNative, Native.sumInteger, accumulatorValue] using hmod
    with_unfolding_all simpa only [pairsFoldCorrection, Bind.bind, Std.bind_assoc, pairs_uncurry_projection, bind_ok] using hspec

#print axioms pairs_uncurry_projection
#print axioms pairs_fold_overflow_spec
end UdonVerify.ProductPairs
