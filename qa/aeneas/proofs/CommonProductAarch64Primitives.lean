import CommonProductAarch64Dictionaries
import CommonProductSliceMath
import NativeProductValue

open Aeneas Std Result
namespace UdonVerify.ProductAarch64
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem aarch64_kernel_dict {M : Type} (inst : Native.Modulus M) :
    aarch64KernelDict (aarch64Dict inst) = Native.kernelInst inst := by rfl

theorem aarch64_adc_bridge (a b carry : U64) :
    CommonProductsAarch64.field.pasta.word.adc a b carry =
      NativeField.zakura_udon.field.pasta.word.adc a b carry := by rfl

theorem aarch64_multiply_wide_bridge (a b : A4) :
    CommonProductsAarch64.field.pasta.word.multiply_wide a b =
      NativeField.zakura_udon.field.pasta.word.multiply_wide a b := by rfl

theorem aarch64_redc_bridge {M : Type} (inst : Native.Modulus M) (wide : A8) :
    CommonProductsAarch64.field.pasta.montgomery.montgomery_reduce_unreduced
      (aarch64Dict inst) wide =
      NativeField.zakura_udon.field.pasta.montgomery.montgomery_reduce_unreduced inst wide := by rfl

theorem aarch64_fold_high_bridge {M : Type} (inst : Native.Modulus M) (wide : A8) (twice : Bool) :
    CommonProductsAarch64.field.pasta.products.fold_high (aarch64Dict inst) wide twice =
      NativeField.zakura_udon.field.pasta.products.fold_high inst wide twice := by rfl

theorem aarch64_is_lt_bridge (order : Ordering) :
    CommonProductsAarch64.core.cmp.Ordering.is_lt order =
      udon_kernel_slice.core.cmp.Ordering.is_lt order := by cases order <;> rfl

theorem aarch64_multiply_loose_bridge {M : Type} (inst : Modulus M) (a b : A4) :
    CommonProductsAarch64.field.pasta.montgomery.montgomery_multiply_loose inst a b =
      udon_kernel_slice.field.pasta.montgomery.montgomery_multiply_loose (aarch64KernelDict inst) a b := by
  unfold CommonProductsAarch64.field.pasta.montgomery.montgomery_multiply_loose
    udon_kernel_slice.field.pasta.montgomery.montgomery_multiply_loose
  simp only [aarch64_is_lt_bridge]
  rfl

@[step]
theorem aarch64_from_montgomery_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (aarch64KernelDict inst)) (limbs : A4)
    (hbound : val4 limbs < 2 * val4 params.modulus) :
    CommonProductsAarch64.field.pasta.PastaField.from_montgomery inst
      CommonProductsAarch64.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState limbs
      ⦃ out => out.limbs = limbs ⦄ := by
  unfold CommonProductsAarch64.field.pasta.PastaField.from_montgomery
    CommonProductsAarch64.field.pasta.PastaField.BOUND
  simp only [
    CommonProductsAarch64.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    bind_ok, Bool.false_eq_true, ite_false]
  have htwice : inst.sealedParametersInst.TWICE_MODULUS = ok params.twice := params.twice_ok
  rw [htwice]
  simp only [bind_ok]
  rw [aarch64_compare_limbs_bridge]
  apply WP.spec_bind (slice_compare_limbs_spec limbs params.twice)
  intro order horder
  have hlt : order = .lt := by
    have ht := params.twice_val
    cases order <;> simp only [orderingRel] at horder ⊢ <;> omega
  simp [hlt, CommonProductsAarch64.core.cmp.Ordering.is_lt, massert, WP.spec_ok]

theorem aarch64_mac_bridge (a b c carry : U64) :
    CommonProductsAarch64.field.pasta.word.mac a b c carry =
      NativeField.zakura_udon.field.pasta.word.mac a b c carry := by rfl

theorem aarch64_partial_reduce_bridge {M : Type} (inst : Native.Modulus M) (sum : Sum M) :
    CommonProductsAarch64.field.pasta.products.ProductSum.partial_reduce (aarch64Dict inst) sum =
      NativeField.zakura_udon.field.pasta.products.ProductSum.partial_reduce inst (sumToNative sum) := by rfl

theorem aarch64_inner_bounded_bridge {M S T : Type} (inst : Native.Modulus M)
    (sum : Sum M) (lhs : Element M S) (rhs : Element M T) :
    CommonProductsAarch64.field.pasta.products.ProductSum.add_product_inner true
      (aarch64Dict inst) sum lhs rhs = (do
        let out ← NativeField.zakura_udon.field.pasta.products.ProductSum.add_product_inner true
          inst (sumToNative sum) (fieldToNative (T := S) lhs) (fieldToNative (T := T) rhs)
        ok (sumFromNative out)) := by
  unfold CommonProductsAarch64.field.pasta.products.ProductSum.add_product_inner
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_product_inner
  simp only [aarch64_mac_bridge, aarch64_adc_bridge, ite_true, Std.bind_assoc, bind_ok, Std.uncurry]
  rfl

@[step]
theorem aarch64_inner_bounded_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (sum : Sum M) (lhs : Element M S) (rhs : Element M T)
    (hbound : sumInteger sum + val4 lhs.limbs * val4 rhs.limbs < B ^ 9) :
    CommonProductsAarch64.field.pasta.products.ProductSum.add_product_inner true
      (aarch64Dict inst) sum lhs rhs ⦃ out =>
        sumInteger out = sumInteger sum + val4 lhs.limbs * val4 rhs.limbs ⦄ := by
  rw [aarch64_inner_bounded_bridge]
  step -grind with (Native.product_inner_spec true inst params constants (sumToNative sum)
    (fieldToNative (T := S) lhs) (fieldToNative (T := T) rhs) (by intro _; exact hbound))
      as ⟨out, hmod, hexact⟩
  exact hexact

@[step]
theorem aarch64_finish_spec {M : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (sum : Sum M) :
    CommonProductsAarch64.field.pasta.products.ProductSum.finish (aarch64Dict inst) sum
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs) (sumInteger sum) ⦄ := by
  unfold CommonProductsAarch64.field.pasta.products.ProductSum.finish
  rw [aarch64_partial_reduce_bridge]
  step -grind with (Native.product_partial_reduce_spec inst params constants (sumToNative sum))
    as ⟨folded, hsmall, hbound, hmod⟩
  rw [aarch64_redc_bridge, Native.redc_unreduced_eq]
  have hredc : val8 folded < val4 params.modulus * R + val4 params.modulus ^ 2 :=
    _root_.lt_of_lt_of_le hbound (Nat.le_add_right _ _)
  step -grind with (montgomery_reduce_unreduced_spec (Native.kernelInst inst) params folded hredc)
    as ⟨limbs, hthree, m, hm, hcert⟩
  have hmp : m * val4 params.modulus < R * val4 params.modulus :=
    Nat.mul_lt_mul_of_pos_right hm params.positive
  have hloose : val4 limbs < 2 * val4 params.modulus := by
    have hmul : R * val4 limbs < R * (2 * val4 params.modulus) := by
      nlinarith only [hcert, hbound, hmp]
    exact Nat.lt_of_mul_lt_mul_left hmul
  step -grind with (aarch64_from_montgomery_loose_spec (aarch64Dict inst) params limbs hloose)
    as ⟨out, hout⟩
  rw [hout]
  exact ⟨hloose, (certificate_congruence _ _ _ _ hcert).trans hmod⟩

#print axioms aarch64_kernel_dict
#print axioms aarch64_adc_bridge
#print axioms aarch64_redc_bridge
#print axioms aarch64_is_lt_bridge
#print axioms aarch64_from_montgomery_loose_spec
#print axioms aarch64_mac_bridge
#print axioms aarch64_partial_reduce_bridge
#print axioms aarch64_inner_bounded_bridge
#print axioms aarch64_inner_bounded_spec
#print axioms aarch64_finish_spec
#print axioms aarch64_multiply_wide_bridge
#print axioms aarch64_fold_high_bridge
#print axioms aarch64_multiply_loose_bridge
@[step]
theorem aarch64_multiply_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (aarch64KernelDict inst)) (lhs : Element M S) (rhs : Element M T)
    (ha : val4 lhs.limbs < 2 * val4 params.modulus)
    (hb : val4 rhs.limbs < 2 * val4 params.modulus) :
    CommonProductsAarch64.field.pasta.PastaField.mul inst lhs rhs ⦃ out =>
      val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs) (val4 lhs.limbs * val4 rhs.limbs) ⦄ := by
  unfold CommonProductsAarch64.field.pasta.PastaField.mul
  rw [aarch64_multiply_loose_bridge]
  step -grind with (montgomery_multiply_loose_spec (aarch64KernelDict inst) params lhs.limbs rhs.limbs ha hb)
    as ⟨limbs, hbound, m, hm, hcert⟩
  step -grind with (aarch64_from_montgomery_loose_spec inst params limbs hbound) as ⟨out, hout⟩
  rw [hout]
  exact ⟨hbound, certificate_congruence _ _ _ _ hcert⟩

#print axioms aarch64_multiply_spec
end UdonVerify.ProductAarch64
