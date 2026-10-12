import CommonPublicInversionHelpers
import NativeConstants

open Aeneas Std Result
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

abbrev Modulus := CommonPublicInversion.field.pasta.parameters.PrimeModulus
abbrev Element := CommonPublicInversion.field.pasta.PastaField
abbrev Loose := CommonPublicInversion.field.pasta.representation.Loose
abbrev Reduced := CommonPublicInversion.field.pasta.representation.Reduced

def fieldFromNative {M S T : Type} (value : Native.Element M S) : Element M T :=
  ⟨value.limbs, ()⟩

def rootsFromNative {M : Type} (values : Array (Native.Element M Native.Reduced) 33#usize) :
    Array (Element M Reduced) 33#usize :=
  Array.from (values.val.map fieldFromNative) (by simp only [List.length_map, values.property])

/-- Retain every constant in the existing production dictionary. Only the
    phantom field types of root-table entries differ between extractions. -/
def publicDict {M : Type} (inst : Native.Modulus M) : Modulus M where
  MODULUS := inst.MODULUS
  sealedSealedInst := ⟨⟩
  coremarkerCopyInst := inst.coremarkerCopyInst
  corecmpEqInst := inst.corecmpEqInst
  sealedParametersInst := {
    ROOTS := do let roots ← inst.sealedParametersInst.ROOTS; ok (rootsFromNative roots)
    INVERSE_ROOTS := do let roots ← inst.sealedParametersInst.INVERSE_ROOTS; ok (rootsFromNative roots)
    TWICE_MODULUS := inst.sealedParametersInst.TWICE_MODULUS
    MONTGOMERY_INV := inst.sealedParametersInst.MONTGOMERY_INV
    R := inst.sealedParametersInst.R
    R2 := inst.sealedParametersInst.R2
    R3 := inst.sealedParametersInst.R3
    B448 := inst.sealedParametersInst.B448
    TWO_INVERSE := inst.sealedParametersInst.TWO_INVERSE
    DELTA := inst.sealedParametersInst.DELTA
    ZETA := inst.sealedParametersInst.ZETA
    ZETA_INVERSE := inst.sealedParametersInst.ZETA_INVERSE
    MODULUS_SIGNED62 := inst.sealedParametersInst.MODULUS_SIGNED62
    POWER_OF_TWO_INVERSES := inst.sealedParametersInst.POWER_OF_TWO_INVERSES
  }

def kernelDict {M : Type} (inst : Modulus M) : udon_kernel_slice.field.pasta.PrimeModulus M :=
  ⟨inst.MODULUS, inst.sealedParametersInst.TWICE_MODULUS, inst.sealedParametersInst.MONTGOMERY_INV⟩

theorem public_reduce_once_bridge {M : Type} (inst : Modulus M) (x : A4) :
    CommonPublicInversion.field.pasta.montgomery.reduce_once inst x =
      udon_kernel_slice.field.pasta.montgomery.reduce_once (kernelDict inst) x := by rfl

theorem public_compare_limbs_bridge (x y : A4) :
    CommonPublicInversion.field.pasta.word.compare_limbs x y =
      udon_kernel_slice.field.pasta.word.compare_limbs x y := by rfl

#print axioms public_reduce_once_bridge
#print axioms public_compare_limbs_bridge
end UdonVerify.PublicInversion
