import CommonPublicInversionDictionaries

open Aeneas Std Result
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem public_reduce_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelDict inst))
    (state : CommonPublicInversion.field.pasta.representation.ReductionState S)
    (reduced : Bool) (hstate : state.sealedSealedInst.REDUCED = ok reduced)
    (value : Element M S)
    (hbound : val4 value.limbs < if reduced then val4 params.modulus else 2 * val4 params.modulus) :
    CommonPublicInversion.field.pasta.PastaField.reduce inst state value ⦃ out =>
      val4 out.limbs < val4 params.modulus ∧ val4 out.limbs = val4 value.limbs % val4 params.modulus ⦄ := by
  unfold CommonPublicInversion.field.pasta.PastaField.reduce
  rw [hstate]
  simp only [bind_ok]
  cases reduced with
  | true =>
    simp only [ite_true] at hbound ⊢
    simp only [WP.spec_ok]
    exact ⟨hbound, (Nat.mod_eq_of_lt hbound).symm⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hbound ⊢
    rw [public_reduce_once_bridge]
    apply WP.spec_bind (reduce_once_spec (kernelDict inst) params value.limbs hbound)
    intro limbs hlimbs
    simpa only [WP.spec_ok] using And.intro hlimbs.2 hlimbs.1

@[step]
theorem public_from_montgomery_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelDict inst)) (limbs : A4)
    (hbound : val4 limbs < 2 * val4 params.modulus) :
    CommonPublicInversion.field.pasta.PastaField.from_montgomery inst
      CommonPublicInversion.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState limbs
      ⦃ out => out.limbs = limbs ⦄ := by
  unfold CommonPublicInversion.field.pasta.PastaField.from_montgomery
    CommonPublicInversion.field.pasta.PastaField.BOUND
  simp only [
    CommonPublicInversion.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    bind_ok, Bool.false_eq_true, ite_false]
  have htwice : inst.sealedParametersInst.TWICE_MODULUS = ok params.twice := params.twice_ok
  rw [htwice]
  simp only [bind_ok]
  rw [public_compare_limbs_bridge]
  apply WP.spec_bind (slice_compare_limbs_spec limbs params.twice)
  intro order horder
  have hlt : order = .lt := by
    have ht := params.twice_val
    cases order <;> simp only [orderingRel] at horder ⊢ <;> omega
  simp [hlt, CommonPublicInversion.core.cmp.Ordering.is_lt, massert, WP.spec_ok]

#print axioms public_reduce_spec
#print axioms public_from_montgomery_loose_spec
end UdonVerify.PublicInversion
