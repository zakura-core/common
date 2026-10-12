import CommonProductShort.Funs
import NativeProductStates

open Aeneas Std Result
namespace UdonVerify.ProductShort
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

abbrev Modulus := CommonProductShort.field.pasta.parameters.PrimeModulus
abbrev Element := CommonProductShort.field.pasta.PastaField
abbrev Loose := CommonProductShort.field.pasta.representation.Loose
abbrev Reduced := CommonProductShort.field.pasta.representation.Reduced

def fieldFromNative {M S T : Type} (value : Native.Element M S) : Element M T :=
  ⟨value.limbs, ()⟩

def rootsFromNative {M : Type} (values : Array (Native.Element M Native.Reduced) 33#usize) :
    Array (Element M Reduced) 33#usize :=
  Array.from (values.val.map fieldFromNative) (by simp only [List.length_map, values.property])

/-- Retain every constant in the existing production dictionary. Only the
    phantom field types of root-table entries differ between extractions. -/
def shortDict {M : Type} (inst : Native.Modulus M) : Modulus M where
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

def shortKernelDict {M : Type} (inst : Modulus M) : udon_kernel_slice.field.pasta.PrimeModulus M :=
  ⟨inst.MODULUS, inst.sealedParametersInst.TWICE_MODULUS, inst.sealedParametersInst.MONTGOMERY_INV⟩

theorem short_reduce_once_bridge {M : Type} (inst : Modulus M) (x : A4) :
    CommonProductShort.zakura_udon.field.pasta.montgomery.reduce_once inst x =
      udon_kernel_slice.field.pasta.montgomery.reduce_once (shortKernelDict inst) x := by rfl

theorem short_compare_limbs_bridge (x y : A4) :
    CommonProductShort.zakura_udon.field.pasta.word.compare_limbs x y =
      udon_kernel_slice.field.pasta.word.compare_limbs x y := by rfl

#print axioms short_reduce_once_bridge
#print axioms short_compare_limbs_bridge
end UdonVerify.ProductShort
