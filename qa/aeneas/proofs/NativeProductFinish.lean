import NativeProductPartial
import RedcProofs

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem product_new_spec (M : Type) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.new M
      ⦃ out => sumInteger out = 0 ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.ProductSum.new
  simp [WP.spec_ok, sumInteger, accumulatorValue, val8]

/-- Every stored accumulator admits successful final reduction below the loose bound. -/
@[step]
theorem product_finish_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (sum : Sum M) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.finish inst sum
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs) (sumInteger sum) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.ProductSum.finish
  step -grind with (product_partial_reduce_spec inst params constants sum)
    as ⟨folded, hsmall, hbound, hmod⟩
  rw [redc_unreduced_eq]
  have hredc : val8 folded < val4 params.modulus * R + val4 params.modulus ^ 2 :=
    _root_.lt_of_lt_of_le hbound (Nat.le_add_right _ _)
  step -grind with (montgomery_reduce_unreduced_spec (kernelInst inst) params folded hredc)
    as ⟨limbs, hthree, m, hm, hcert⟩
  have hmp : m * val4 params.modulus < R * val4 params.modulus :=
    Nat.mul_lt_mul_of_pos_right hm params.positive
  have hloose : val4 limbs < 2 * val4 params.modulus := by
    have hmul : R * val4 limbs < R * (2 * val4 params.modulus) := by
      nlinarith only [hcert, hbound, hmp]
    exact Nat.lt_of_mul_lt_mul_left hmul
  step -grind with (from_montgomery_loose_spec inst params limbs hloose) as ⟨out, hout⟩
  rw [hout]
  exact ⟨hloose, (certificate_congruence _ _ _ _ hcert).trans hmod⟩

theorem decoded_product_sum (p inverse total value : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hcert : Nat.ModEq p (R * value) total) :
    (value * inverse) % p = (total * inverse ^ 2) % p := by
  have hscaled : Nat.ModEq p ((R * inverse) * (value * inverse)) (total * inverse ^ 2) := by
    convert hcert.mul_right (inverse ^ 2) using 1 <;> ring
  have hcancel : Nat.ModEq p ((R * inverse) * (value * inverse)) (value * inverse) := by
    simpa only [one_mul] using hinverse.mul_right (value * inverse)
  exact hcancel.symm.trans hscaled

@[step]
theorem product_finish_value_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (sum : Sum M) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.finish inst sum
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs = sumValue (val4 params.modulus) inverse sum ⦄ := by
  step -grind with (product_finish_spec inst params constants sum) as ⟨out, hbound, hcert⟩
  exact ⟨hbound, decoded_product_sum _ _ _ _ hinverse hcert⟩

#print axioms product_new_spec
#print axioms product_finish_spec
#print axioms decoded_product_sum
#print axioms product_finish_value_spec

end UdonVerify.Native
