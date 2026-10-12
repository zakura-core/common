import CommonPublicInversionResult
import CommonPublicInversionRepresentation
import CommonPublicInversionMath

open Aeneas Std Result UdonVerify.CommonSigned62
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def FieldInversionResult {M S : Type} (p inverse : Nat) (value : Element M S)
    (out : Option (Element M Loose)) : Prop :=
  match out with
  | none => Native.decode p inverse value.limbs = 0
  | some result => Native.decode p inverse value.limbs ≠ 0 ∧ val4 result.limbs < p ∧
    (Native.decode p inverse value.limbs * Native.decode p inverse result.limbs) % p = 1

@[step]
theorem public_invert_conditional_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelDict inst))
    (invParams : InversionParameters (coreDict (CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket inst)))
    (hmodulus : signed62Value invParams.helpers.modulus = (val4 params.modulus : Int))
    (hprime : Nat.Prime (val4 params.modulus)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (state : CommonPublicInversion.field.pasta.representation.ReductionState S)
    (reduced : Bool) (hstate : state.sealedSealedInst.REDUCED = ok reduced)
    (value : Element M S)
    (hbound : val4 value.limbs < if reduced then val4 params.modulus else 2 * val4 params.modulus)
    (hconverges : ∀ n : Nat, n < val4 params.modulus →
      (inversionTrace (signed62Value invParams.helpers.modulus) (n : Int) 12).g = 0) :
    CommonPublicInversion.field.pasta.inversion.PastaField.invert inst state value ⦃ out =>
      FieldInversionResult (val4 params.modulus) inverse value out ⦄ := by
  unfold CommonPublicInversion.field.pasta.inversion.PastaField.invert
  apply WP.spec_bind (public_reduce_spec inst params state reduced hstate value hbound)
  intro canonical hcanonical
  rcases hcanonical with ⟨hcanonical, hstored⟩
  have hdecoded : Native.decode (val4 params.modulus) inverse canonical.limbs =
      Native.decode (val4 params.modulus) inverse value.limbs := by
    unfold Native.decode
    rw [hstored]
    exact Native.decoded_reduce _ _ _
  have hzero : Native.decode (val4 params.modulus) inverse value.limbs = 0 ↔ val4 canonical.limbs = 0 := by
    rw [← hdecoded]
    unfold Native.decode
    rw [Native.decoded_zero_iff _ _ _ hinverse, Nat.mod_eq_of_lt hcanonical]
  apply WP.spec_bind (public_core_invert_conditional_spec
    (CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket inst) invParams canonical.limbs
    (by rw [hmodulus]; exact_mod_cast hcanonical)
    (by
      intro hnz
      rw [hmodulus]
      exact canonical_input_is_unit _ _ hprime hcanonical hnz)
    (hconverges _ hcanonical))
  intro core hcore
  cases core with
  | none =>
    change val4 canonical.limbs = 0 at hcore
    simp only [CommonPublicInversion.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      CommonPublicInversion.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,
      bind_ok, WP.spec_ok, FieldInversionResult]
    exact hzero.mpr hcore
  | some limbs =>
    change val4 canonical.limbs ≠ 0 ∧ InversionResult invParams (val4 canonical.limbs : Int) limbs at hcore
    have houtBound : val4 limbs < val4 params.modulus := by
      have h := hcore.2.1
      rw [hmodulus] at h
      exact_mod_cast h
    have hweighted := hcore.2.2
    rw [hmodulus] at hweighted
    simp only [CommonPublicInversion.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
    apply WP.spec_bind (public_from_montgomery_loose_spec inst params limbs (by omega))
    intro out hout
    simp only [WP.spec_ok, FieldInversionResult, hout]
    refine ⟨fun h => hcore.1 (hzero.mp h), houtBound, ?_⟩
    rw [← hdecoded]
    exact weighted_inverse_decodes _ _ _ _ hprime.one_lt hinverse hweighted

#print axioms public_invert_conditional_spec
end UdonVerify.PublicInversion
