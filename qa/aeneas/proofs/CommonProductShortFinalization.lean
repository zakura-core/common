import CommonProductShortPrimitives

open Aeneas Std Result
namespace UdonVerify.ProductShort
open UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def finish {M : Type} (inst : Native.Modulus M) (s t : Bool) (wide : A8) : Result (Element M Loose) := do
  let folded ← if !s || !t then
    CommonProductShort.zakura_udon.field.pasta.products.fold_high (shortDict inst) wide (!s && !t)
    else ok wide
  let out ← CommonProductShort.zakura_udon.field.pasta.montgomery.montgomery_reduce_unreduced
    (shortDict inst) folded
  CommonProductShort.zakura_udon.field.pasta.PastaField.from_montgomery (shortDict inst)
    CommonProductShort.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState out

@[step]
theorem finish_spec {M : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (s t : Bool) (wide : A8)
    (hbound : val8 wide < (stateWeight s * stateWeight t) * val4 params.modulus * R) :
    finish inst s t wide ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (R * val4 out.limbs) (val8 wide) ⦄ := by
  have hfold : (if !s || !t then
      CommonProductShort.zakura_udon.field.pasta.products.fold_high (shortDict inst) wide (!s && !t)
      else ok wide) ⦃ out => val8 out < val4 params.modulus * R ∧
        Nat.ModEq (val4 params.modulus) (val8 out) (val8 wide) ⦄ := by
    simp only [short_fold_high_bridge]
    by_cases h : (!s || !t) = true
    · rw [if_pos h]
      exact Native.product_fold_high_spec inst params wide (!s && !t)
        (short_sum_high_bound wide (val4 params.modulus) s t hbound h)
    · rw [if_neg h]
      simp only [WP.spec_ok]
      have hs : s = true := by cases s <;> simp_all
      have ht : t = true := by cases t <;> simp_all
      exact ⟨by simpa [hs, ht, stateWeight] using hbound, Nat.ModEq.refl _⟩
  unfold finish
  step -grind with hfold as ⟨folded,hsmall,hmod⟩
  rw [short_redc_bridge, Native.redc_unreduced_eq]
  have hredc : val8 folded < val4 params.modulus * R + val4 params.modulus ^ 2 :=
    _root_.lt_of_lt_of_le hsmall (Nat.le_add_right _ _)
  step -grind with (montgomery_reduce_unreduced_spec (Native.kernelInst inst) params folded hredc)
    as ⟨limbs,hthree,m,hm,hcert⟩
  have hmp : m * val4 params.modulus < R * val4 params.modulus :=
    Nat.mul_lt_mul_of_pos_right hm params.positive
  have hloose : val4 limbs < 2 * val4 params.modulus := by
    have hmul : R * val4 limbs < R * (2 * val4 params.modulus) := by
      nlinarith only [hcert,hsmall,hmp]
    exact Nat.lt_of_mul_lt_mul_left hmul
  step -grind with (short_from_montgomery_loose_spec (shortDict inst) params limbs hloose) as ⟨out,hout⟩
  rw [hout]
  exact ⟨hloose,(certificate_congruence _ _ _ _ hcert).trans hmod⟩

#print axioms finish_spec
end UdonVerify.ProductShort
