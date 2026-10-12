import CommonProductSliceMath
import NativeProductFinish

open Aeneas Std Result
namespace UdonVerify.Products
open UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The native finalization selected by the two input representation states. -/
def shortFinish {M : Type} (inst : Modulus M) (s t : Bool) (wide : A8) :
    Result (Element M Loose) := do
  let folded ← if !s || !t then
    NativeField.zakura_udon.field.pasta.products.fold_high inst wide (!s && !t)
    else ok wide
  let out ← NativeField.zakura_udon.field.pasta.montgomery.montgomery_reduce_unreduced inst folded
  NativeField.zakura_udon.field.pasta.PastaField.from_montgomery inst looseInst out

@[step]
theorem short_finish_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (s t : Bool) (wide : A8)
    (hbound : val8 wide < (stateWeight s * stateWeight t) * val4 params.modulus * R) :
    shortFinish inst s t wide
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs) (val8 wide) ⦄ := by
  have hfold : (if !s || !t then
      NativeField.zakura_udon.field.pasta.products.fold_high inst wide (!s && !t)
      else ok wide)
      ⦃ out => val8 out < val4 params.modulus * R ∧
        Nat.ModEq (val4 params.modulus) (val8 out) (val8 wide) ⦄ := by
    by_cases h : (!s || !t) = true
    · rw [if_pos h]
      exact product_fold_high_spec inst params wide (!s && !t)
        (short_sum_high_bound wide (val4 params.modulus) s t hbound h)
    · rw [if_neg h]
      simp only [WP.spec_ok]
      have hs : s = true := by cases s <;> simp_all
      have ht : t = true := by cases t <;> simp_all
      exact ⟨by simpa [hs, ht, stateWeight] using hbound, Nat.ModEq.refl _⟩
  unfold shortFinish
  step -grind with hfold as ⟨folded, hsmall, hmod⟩
  rw [redc_unreduced_eq]
  have hredc : val8 folded < val4 params.modulus * R + val4 params.modulus ^ 2 :=
    _root_.lt_of_lt_of_le hsmall (Nat.le_add_right _ _)
  step -grind with (montgomery_reduce_unreduced_spec (kernelInst inst) params folded hredc)
    as ⟨limbs, hthree, m, hm, hcert⟩
  have hmp : m * val4 params.modulus < R * val4 params.modulus :=
    Nat.mul_lt_mul_of_pos_right hm params.positive
  have hloose : val4 limbs < 2 * val4 params.modulus := by
    have hmul : R * val4 limbs < R * (2 * val4 params.modulus) := by
      nlinarith only [hcert, hsmall, hmp]
    exact Nat.lt_of_mul_lt_mul_left hmul
  step -grind with (from_montgomery_loose_spec inst params limbs hloose) as ⟨out, hout⟩
  rw [hout]
  exact ⟨hloose, (certificate_congruence _ _ _ _ hcert).trans hmod⟩

@[step]
theorem short_finish_value_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (s t : Bool) (wide : A8)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (hbound : val8 wide < (stateWeight s * stateWeight t) * val4 params.modulus * R) :
    shortFinish inst s t wide
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs =
          (val8 wide * inverse ^ 2) % val4 params.modulus ⦄ := by
  step -grind with (short_finish_spec inst params s t wide hbound) as ⟨out, hbound, hcert⟩
  exact ⟨hbound, decoded_product_sum _ _ _ _ hinverse hcert⟩

#print axioms short_finish_spec
#print axioms short_finish_value_spec
end UdonVerify.Products
