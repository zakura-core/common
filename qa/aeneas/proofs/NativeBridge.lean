import NativeField.Funs
import MontgomeryMultiply
import LooseMultiplyPublic
import LooseAdd
import LooseSub
import CompareProofs
import MontgomeryWrappers

open Aeneas Std Result

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

namespace Native

abbrev Modulus := NativeField.zakura_udon.field.pasta.parameters.PrimeModulus
abbrev Element := NativeField.zakura_udon.field.pasta.PastaField
abbrev Loose := NativeField.zakura_udon.field.pasta.representation.Loose
abbrev Reduced := NativeField.zakura_udon.field.pasta.representation.Reduced
abbrev Base := NativeField.zakura_udon.field.pasta.parameters.PallasBase
abbrev Scalar := NativeField.zakura_udon.field.pasta.parameters.PallasScalar

def kernelInst {M : Type} (inst : Modulus M) :
    udon_kernel_slice.field.pasta.PrimeModulus M where
  MODULUS := inst.MODULUS
  TWICE_MODULUS := inst.sealedParametersInst.TWICE_MODULUS
  MONTGOMERY_INV := inst.sealedParametersInst.MONTGOMERY_INV

theorem compare_eq (lhs rhs : A4) :
    NativeField.zakura_udon.field.pasta.word.compare_limbs lhs rhs =
      udon_kernel_slice.field.pasta.word.compare_limbs lhs rhs := by
  rfl

theorem multiply_loose_eq {M : Type} (inst : Modulus M) (lhs rhs : A4) :
    NativeField.zakura_udon.field.pasta.montgomery.montgomery_multiply_loose inst lhs rhs =
      udon_kernel_slice.field.pasta.montgomery.montgomery_multiply_loose (kernelInst inst) lhs rhs := by
  rfl

theorem square_eq {M : Type} (inst : Modulus M) (limbs : A4) :
    NativeField.zakura_udon.field.pasta.montgomery.montgomery_square inst limbs =
      udon_kernel_slice.field.pasta.montgomery.montgomery_square (kernelInst inst) limbs := by
  rfl

theorem reduce_once_eq {M : Type} (inst : Modulus M) (limbs : A4) :
    NativeField.zakura_udon.field.pasta.montgomery.reduce_once inst limbs =
      udon_kernel_slice.field.pasta.montgomery.reduce_once (kernelInst inst) limbs := by
  rfl

theorem reduce_twice_eq {M : Type} (inst : Modulus M) (limbs : A4) (carry : U64) :
    NativeField.zakura_udon.field.pasta.montgomery.reduce_twice_modulus inst limbs carry =
      udon_kernel_slice.field.pasta.montgomery.reduce_twice_modulus (kernelInst inst) limbs carry := by
  rfl

theorem add_limbs_eq (lhs rhs : A4) :
    NativeField.zakura_udon.field.pasta.word.add_limbs lhs rhs =
      udon_kernel_slice.field.pasta.word.add_limbs lhs rhs := by
  rfl

theorem subtract_limbs_eq (lhs rhs : A4) :
    NativeField.zakura_udon.field.pasta.word.subtract_limbs lhs rhs =
      udon_kernel_slice.field.pasta.word.subtract_limbs lhs rhs := by
  rfl

theorem mac_eq (accumulator lhs rhs carry : U64) :
    NativeField.zakura_udon.field.pasta.word.mac accumulator lhs rhs carry =
      udon_kernel_slice.field.pasta.word.mac accumulator lhs rhs carry := by
  rfl

theorem sbb_eq (lhs rhs borrow : U64) :
    NativeField.zakura_udon.field.pasta.word.sbb lhs rhs borrow =
      udon_kernel_slice.field.pasta.word.sbb lhs rhs borrow := by
  rfl

theorem add_twice_eq {M : Type} (inst : Modulus M) (lhs rhs : A4) :
    NativeField.zakura_udon.field.pasta.montgomery.add_twice_modulus inst lhs rhs =
      udon_kernel_slice.field.pasta.montgomery.add_twice_modulus (kernelInst inst) lhs rhs := by
  rfl

theorem sub_twice_eq {M : Type} (inst : Modulus M) (lhs rhs : A4) :
    NativeField.zakura_udon.field.pasta.montgomery.sub_twice_modulus inst lhs rhs =
      udon_kernel_slice.field.pasta.montgomery.sub_twice_modulus (kernelInst inst) lhs rhs := by
  rfl

def transferParameters {M N : Type}
    {source : udon_kernel_slice.field.pasta.PrimeModulus M}
    (target : udon_kernel_slice.field.pasta.PrimeModulus N)
    (params : PastaParameters source)
    (hm : target.MODULUS = ok params.modulus)
    (ht : target.TWICE_MODULUS = ok params.twice)
    (hi : target.MONTGOMERY_INV = ok params.inv) : PastaParameters target where
  modulus := params.modulus
  twice := params.twice
  inv := params.inv
  modulus_ok := hm
  twice_ok := ht
  inv_ok := hi
  zero_limb := params.zero_limb
  high_limb := params.high_limb
  inverse := params.inverse
  twice_val := params.twice_val
  positive := params.positive
  offset_positive := params.offset_positive
  offset_small := params.offset_small
  thrice_lt := params.thrice_lt

abbrev fpNativeInst :=
  NativeField.zakura_udon.field.pasta.parameters.PallasBase.Insts.Zakura_udonFieldPastaParametersPrimeModulus
abbrev fqNativeInst :=
  NativeField.zakura_udon.field.pasta.parameters.PallasScalar.Insts.Zakura_udonFieldPastaParametersPrimeModulus

def fpNativeParameters : PastaParameters (kernelInst fpNativeInst) :=
  transferParameters (kernelInst fpNativeInst) fpParameters
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

def fqNativeParameters : PastaParameters (kernelInst fqNativeInst) :=
  transferParameters (kernelInst fqNativeInst) fqParameters
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)

end Native
end UdonVerify
