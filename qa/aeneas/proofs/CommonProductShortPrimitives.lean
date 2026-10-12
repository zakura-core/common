import CommonProductShortDictionaries
import CommonProductShortFinish

open Aeneas Std Result
namespace UdonVerify.ProductShort
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem short_kernel_dict {M : Type} (inst : Native.Modulus M) :
    shortKernelDict (shortDict inst) = Native.kernelInst inst := by rfl

theorem short_adc_bridge (a b carry : U64) :
    CommonProductShort.zakura_udon.field.pasta.word.adc a b carry =
      NativeField.zakura_udon.field.pasta.word.adc a b carry := by rfl

theorem short_multiply_wide_bridge (a b : A4) :
    CommonProductShort.zakura_udon.field.pasta.word.multiply_wide a b =
      NativeField.zakura_udon.field.pasta.word.multiply_wide a b := by rfl

theorem short_redc_bridge {M : Type} (inst : Native.Modulus M) (wide : A8) :
    CommonProductShort.zakura_udon.field.pasta.montgomery.montgomery_reduce_unreduced
      (shortDict inst) wide =
      NativeField.zakura_udon.field.pasta.montgomery.montgomery_reduce_unreduced inst wide := by rfl

theorem short_fold_high_bridge {M : Type} (inst : Native.Modulus M) (wide : A8) (twice : Bool) :
    CommonProductShort.zakura_udon.field.pasta.products.fold_high (shortDict inst) wide twice =
      NativeField.zakura_udon.field.pasta.products.fold_high inst wide twice := by rfl

theorem short_is_lt_bridge (order : Ordering) :
    CommonProductShort.core.cmp.Ordering.is_lt order =
      udon_kernel_slice.core.cmp.Ordering.is_lt order := by cases order <;> rfl

theorem short_multiply_loose_bridge {M : Type} (inst : Modulus M) (a b : A4) :
    CommonProductShort.zakura_udon.field.pasta.montgomery.montgomery_multiply_loose inst a b =
      udon_kernel_slice.field.pasta.montgomery.montgomery_multiply_loose (shortKernelDict inst) a b := by
  unfold CommonProductShort.zakura_udon.field.pasta.montgomery.montgomery_multiply_loose
    udon_kernel_slice.field.pasta.montgomery.montgomery_multiply_loose
  simp only [short_is_lt_bridge]
  rfl

@[step]
theorem short_from_montgomery_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (shortKernelDict inst)) (limbs : A4)
    (hbound : val4 limbs < 2 * val4 params.modulus) :
    CommonProductShort.zakura_udon.field.pasta.PastaField.from_montgomery inst
      CommonProductShort.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState limbs
      ⦃ out => out.limbs = limbs ⦄ := by
  unfold CommonProductShort.zakura_udon.field.pasta.PastaField.from_montgomery
    CommonProductShort.field.pasta.PastaField.BOUND
  simp only [
    CommonProductShort.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    bind_ok, Bool.false_eq_true, ite_false]
  have htwice : inst.sealedParametersInst.TWICE_MODULUS = ok params.twice := params.twice_ok
  rw [htwice]
  simp only [bind_ok]
  rw [short_compare_limbs_bridge]
  apply WP.spec_bind (slice_compare_limbs_spec limbs params.twice)
  intro order horder
  have hlt : order = .lt := by
    have ht := params.twice_val
    cases order <;> simp only [orderingRel] at horder ⊢ <;> omega
  simp [hlt, CommonProductShort.core.cmp.Ordering.is_lt, massert, WP.spec_ok]

@[step]
theorem short_multiply_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (shortKernelDict inst)) (lhs : Element M S) (rhs : Element M T)
    (ha : val4 lhs.limbs < 2 * val4 params.modulus)
    (hb : val4 rhs.limbs < 2 * val4 params.modulus) :
    CommonProductShort.zakura_udon.field.pasta.PastaField.mul inst lhs rhs ⦃ out =>
      val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs) (val4 lhs.limbs * val4 rhs.limbs) ⦄ := by
  unfold CommonProductShort.zakura_udon.field.pasta.PastaField.mul
  rw [short_multiply_loose_bridge]
  step -grind with (montgomery_multiply_loose_spec (shortKernelDict inst) params lhs.limbs rhs.limbs ha hb)
    as ⟨limbs, hbound, m, hm, hcert⟩
  step -grind with (short_from_montgomery_loose_spec inst params limbs hbound) as ⟨out, hout⟩
  rw [hout]
  exact ⟨hbound, certificate_congruence _ _ _ _ hcert⟩

#print axioms short_kernel_dict
#print axioms short_adc_bridge
#print axioms short_multiply_wide_bridge
#print axioms short_redc_bridge
#print axioms short_fold_high_bridge
#print axioms short_is_lt_bridge
#print axioms short_multiply_loose_bridge
#print axioms short_from_montgomery_loose_spec
#print axioms short_multiply_spec
end UdonVerify.ProductShort
