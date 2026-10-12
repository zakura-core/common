import CommonPublicInversionDictionaries
import NativeBasics

open Aeneas Std Result
namespace UdonVerify.PublicInversion

/-- Preserve every method and flag of the production representation dictionary. -/
def publicState {S : Type}
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S) :
    CommonPublicInversion.field.pasta.representation.ReductionState S where
  sealedSealedInst := ⟨state.sealedSealedInst.REDUCED⟩
  coremarkerCopyInst := state.coremarkerCopyInst
  corecmpEqInst := state.corecmpEqInst

abbrev looseInputInst := publicState Native.looseInst
abbrev reducedInputInst := publicState Native.reducedInst

theorem public_state_flag {S : Type}
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S) :
    (publicState state).sealedSealedInst.REDUCED = state.sealedSealedInst.REDUCED := by rfl

#print axioms public_state_flag
end UdonVerify.PublicInversion
