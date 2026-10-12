import Common
import KernelBridge
import Algebra

open Aeneas Std Result
open udon_kernel_slice.field.pasta

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

structure PastaParameters {M : Type} (inst : PrimeModulus M) where
  modulus : A4
  twice : A4
  inv : U64
  modulus_ok : inst.MODULUS = ok modulus
  twice_ok : inst.TWICE_MODULUS = ok twice
  inv_ok : inst.MONTGOMERY_INV = ok inv
  zero_limb : modulus[2]!.val = 0
  high_limb : modulus[3]!.val = 2^62
  inverse : (modulus[0]!.val * inv.val + 1) % B = 0
  twice_val : val4 twice = 2 * val4 modulus
  positive : 0 < val4 modulus
  offset_positive : R/4 < val4 modulus
  offset_small : 16 * (val4 modulus - R/4)^2 < R
  thrice_lt : 3 * val4 modulus < R

abbrev fpInst := PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus
abbrev fqInst := PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus

def fpParameters : PastaParameters fpInst where
  modulus := PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS
  twice := PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.TWICE_MODULUS
  inv := PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MONTGOMERY_INV
  modulus_ok := rfl
  twice_ok := rfl
  inv_ok := rfl
  zero_limb := by
    simp [PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]
  high_limb := by
    simp [PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]
  inverse := by
    norm_num [PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS,
      PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MONTGOMERY_INV, B]
  twice_val := by
    norm_num [PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS,
      PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.TWICE_MODULUS, val4, B]
  positive := by
    norm_num [PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS, val4, B]
  offset_positive := by
    norm_num [PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS, val4, R, B]
  offset_small := by
    norm_num [PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS, val4, R, B]
  thrice_lt := by
    norm_num [PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS, val4, R, B]

def fqParameters : PastaParameters fqInst where
  modulus := PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS
  twice := PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.TWICE_MODULUS
  inv := PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MONTGOMERY_INV
  modulus_ok := rfl
  twice_ok := rfl
  inv_ok := rfl
  zero_limb := by
    simp [PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]
  high_limb := by
    simp [PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]
  inverse := by
    norm_num [PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS,
      PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MONTGOMERY_INV, B]
  twice_val := by
    norm_num [PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS,
      PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.TWICE_MODULUS, val4, B]
  positive := by
    norm_num [PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS, val4, B]
  offset_positive := by
    norm_num [PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS, val4, R, B]
  offset_small := by
    norm_num [PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS, val4, R, B]
  thrice_lt := by
    norm_num [PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS, val4, R, B]

end UdonVerify
