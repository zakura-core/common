import CommonProductsAarch64.Funs
import NativeProductStates

open Aeneas Std Result
namespace UdonVerify.ProductAarch64
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

abbrev Modulus := CommonProductsAarch64.field.pasta.parameters.PrimeModulus
abbrev Element := CommonProductsAarch64.field.pasta.PastaField
abbrev Loose := CommonProductsAarch64.field.pasta.representation.Loose
abbrev Reduced := CommonProductsAarch64.field.pasta.representation.Reduced

def fieldFromNative {M S T : Type} (value : Native.Element M S) : Element M T :=
  ⟨value.limbs, ()⟩

def rootsFromNative {M : Type} (values : Array (Native.Element M Native.Reduced) 33#usize) :
    Array (Element M Reduced) 33#usize :=
  Array.from (values.val.map fieldFromNative) (by simp only [List.length_map, values.property])

/-- Retain every constant in the existing production dictionary. Only the
    phantom field types of root-table entries differ between extractions. -/
def aarch64Dict {M : Type} (inst : Native.Modulus M) : Modulus M where
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

def aarch64KernelDict {M : Type} (inst : Modulus M) : udon_kernel_slice.field.pasta.PrimeModulus M :=
  ⟨inst.MODULUS, inst.sealedParametersInst.TWICE_MODULUS, inst.sealedParametersInst.MONTGOMERY_INV⟩

theorem aarch64_reduce_once_bridge {M : Type} (inst : Modulus M) (x : A4) :
    CommonProductsAarch64.field.pasta.montgomery.reduce_once inst x =
      udon_kernel_slice.field.pasta.montgomery.reduce_once (aarch64KernelDict inst) x := by rfl

theorem aarch64_compare_limbs_bridge (x y : A4) :
    CommonProductsAarch64.field.pasta.word.compare_limbs x y =
      udon_kernel_slice.field.pasta.word.compare_limbs x y := by rfl

#print axioms aarch64_reduce_once_bridge
#print axioms aarch64_compare_limbs_bridge
abbrev Sum := CommonProductsAarch64.field.pasta.products.ProductSum

def sumFromNative {M : Type} (value : Native.Sum M) : Sum M :=
  ⟨value.wide, value.carry, ()⟩

def sumToNative {M : Type} (value : Sum M) : Native.Sum M :=
  ⟨value.wide, value.carry, ()⟩

def fieldToNative {M S T : Type} (value : Element M S) : Native.Element M T :=
  ⟨value.limbs, ()⟩

def sumInteger {M : Type} (sum : Sum M) : Nat := Native.sumInteger (sumToNative sum)

theorem sum_round_trip {M : Type} (sum : Sum M) : sumFromNative (sumToNative sum) = sum := by
  rcases sum with ⟨wide, carry, marker⟩
  cases marker
  rfl

#print axioms sum_round_trip
end UdonVerify.ProductAarch64
