import KernelSlice.Funs
import Common
import WordPrimitives
import LimbProofs
import SubtractProofs
import CompareProofs
import WideMultiply
import SquareProofs
import FlagLimbProofs

open Aeneas Std Result

namespace UdonVerify

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem slice_adc_identity (lhs rhs carry : U64) :
    udon_kernel_slice.field.pasta.word.adc lhs rhs carry ⦃ lo hi =>
      lo.val + B * hi.val = lhs.val + rhs.val + carry.val ⦄ := by
  simpa only [udon_kernel_slice.field.pasta.word.adc,
    zakura_udon.field.pasta.word.adc] using adc_identity lhs rhs carry

@[step]
theorem slice_mac_identity (accumulator lhs rhs carry : U64) :
    udon_kernel_slice.field.pasta.word.mac accumulator lhs rhs carry ⦃ lo hi =>
      lo.val + B * hi.val = lhs.val * rhs.val + accumulator.val + carry.val ⦄ := by
  simpa only [udon_kernel_slice.field.pasta.word.mac,
    zakura_udon.field.pasta.word.mac] using mac_identity accumulator lhs rhs carry

@[step]
theorem slice_sbb_identity (lhs rhs borrow : U64) (hb : borrow.val ≤ 1) :
    udon_kernel_slice.field.pasta.word.sbb lhs rhs borrow ⦃ out =>
      out.2.val ≤ 1 ∧ out.1.val + rhs.val + borrow.val = lhs.val + B * out.2.val ⦄ := by
  simpa only [udon_kernel_slice.field.pasta.word.sbb,
    zakura_udon.field.pasta.word.sbb] using sbb_spec lhs rhs borrow hb

@[step]
theorem slice_carry_add_spec (lhs rhs : U64) (carry : Bool) :
    udon_kernel_slice.field.pasta.word.carry_add lhs rhs carry ⦃ out =>
      out.1.val + B * out.2.toNat = lhs.val + rhs.val + carry.toNat ⦄ := by
  simpa only [udon_kernel_slice.field.pasta.word.carry_add,
    zakura_udon.field.pasta.word.carry_add] using CommonVerify.carry_add_spec lhs rhs carry

@[step]
theorem slice_wide_mul_spec (lhs rhs : U64) :
    udon_kernel_slice.field.pasta.word.wide_mul lhs rhs ⦃ out =>
      out.1.val = (lhs.val * rhs.val) % B ∧
      out.2.val = (lhs.val * rhs.val) / B ⦄ := by
  simpa only [udon_kernel_slice.field.pasta.word.wide_mul,
    zakura_udon.field.pasta.word.wide_mul] using CommonVerify.wide_mul_spec lhs rhs

@[step]
theorem slice_wide_mul_identity (lhs rhs : U64) :
    udon_kernel_slice.field.pasta.word.wide_mul lhs rhs ⦃ lo hi =>
      lo.val + B * hi.val = lhs.val * rhs.val ⦄ := by
  step with slice_wide_mul_spec as ⟨lo, hi, hlo, hhi⟩
  have hd := Nat.mod_add_div (lhs.val * rhs.val) B
  simp only [B] at *
  omega

@[step]
theorem slice_add_limbs_spec (lhs rhs : A4) :
    udon_kernel_slice.field.pasta.word.add_limbs lhs rhs ⦃ out carry =>
      carry.val ≤ 1 ∧ val4 out + R * carry.val = val4 lhs + val4 rhs ⦄ := by
  with_unfolding_all exact (add_limbs_spec lhs rhs)

@[step]
theorem slice_subtract_limbs_spec (lhs rhs : A4) :
    udon_kernel_slice.field.pasta.word.subtract_limbs lhs rhs ⦃ out borrow =>
      borrow.val ≤ 1 ∧ val4 out + val4 rhs = val4 lhs + R * borrow.val ⦄ := by
  with_unfolding_all exact (subtract_limbs_spec lhs rhs)

@[step]
theorem slice_compare_limbs_spec (lhs rhs : A4) :
    udon_kernel_slice.field.pasta.word.compare_limbs lhs rhs ⦃ out =>
      orderingRel out (val4 lhs) (val4 rhs) ⦄ := by
  with_unfolding_all exact (compare_limbs_spec lhs rhs)

@[step]
theorem slice_multiply_wide_spec (lhs rhs : A4) :
    udon_kernel_slice.field.pasta.word.multiply_wide lhs rhs ⦃ out =>
      val8 out = val4 lhs * val4 rhs ⦄ := by
  with_unfolding_all exact (multiply_wide_spec lhs rhs)

@[step]
theorem slice_square_wide_spec (value : A4) :
    udon_kernel_slice.field.pasta.word.square_wide value ⦃ out =>
      val8 out = val4 value ^ 2 ⦄ := by
  with_unfolding_all exact (square_wide_spec value)

@[step]
theorem slice_carry_add_limbs_spec (lhs rhs : A4) :
    udon_kernel_slice.field.pasta.word.carry_add_limbs lhs rhs ⦃ out =>
      val4 out.1 + R * out.2.toNat = val4 lhs + val4 rhs ⦄ := by
  with_unfolding_all exact (carry_add_limbs_spec lhs rhs)

@[step]
theorem slice_borrow_sub_limbs_spec (lhs rhs : A4) :
    udon_kernel_slice.field.pasta.word.borrow_sub_limbs lhs rhs ⦃ out =>
      val4 out.1 + val4 rhs = val4 lhs + R * out.2.toNat ⦄ := by
  with_unfolding_all exact (borrow_sub_limbs_spec lhs rhs)

end UdonVerify
