import NativeWideAdd
import NativeProductMath
import WideMultiply

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Two raw products are added without truncation and reduced by the native REDC kernel. -/
@[step]
theorem raw_product_sum_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (a b c d : A4)
    (hbound : val4 a * val4 b + val4 c * val4 d < val4 params.modulus * R) :
    NativeField.zakura_udon.field.pasta.encoding.raw_product_sum inst a b c d
      ⦃ out => val4 out < 2 * val4 params.modulus ∧
        ∃ m : Nat, m < R ∧
          R * val4 out = val4 a * val4 b + val4 c * val4 d + m * val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.raw_product_sum
  rw [wide_multiply_eq]
  step -grind with (slice_multiply_wide_spec a b) as ⟨ab, hab⟩
  rw [wide_multiply_eq]
  step -grind with (slice_multiply_wide_spec c d) as ⟨cd, hcd⟩
  simp only [Array.to_slice_mut, lift, bind_ok, core.slice.Slice.iter_mut,
    mutableZipCtor,
    _root_.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter]
  have hloop := raw_add_loop_spec ab cd
  simp only [Array.to_slice] at hloop ⊢
  step -grind with hloop as ⟨carry, back, hadd⟩
  let sum := Array.from_slice ab back.fst.slice
  try dsimp only at hadd ⊢
  have hR : 0 < R := by norm_num [R, B]
  have htotal : val4 a * val4 b + val4 c * val4 d < R ^ 2 := by
    have hpr := Nat.mul_lt_mul_of_pos_right (val4_lt params.modulus) hR
    nlinarith only [hbound, hpr]
  have hzeroVal : carry.val = 0 := by
    rw [hab, hcd] at hadd
    nlinarith only [hadd, htotal]
  have hsum : val8 sum = val4 a * val4 b + val4 c * val4 d := by
    simpa only [hab, hcd, hzeroVal, mul_zero, add_zero] using hadd
  have hzero : carry = 0#u64 := by scalar_tac
  subst carry
  step -grind
  rw [redc_unreduced_eq]
  have hredc : val8 sum < val4 params.modulus * R + val4 params.modulus ^ 2 := by
    rw [hsum]
    exact _root_.lt_of_lt_of_le hbound (Nat.le_add_right _ _)
  step -grind with (montgomery_reduce_unreduced_spec (kernelInst inst) params sum hredc)
    as ⟨out, hthree, m, hm, hcert⟩
  change R * val4 out = val8 sum + m * val4 params.modulus at hcert
  have hmp : m * val4 params.modulus < R * val4 params.modulus :=
    Nat.mul_lt_mul_of_pos_right hm params.positive
  have hout : val4 out < 2 * val4 params.modulus := by
    have hmul : R * val4 out < R * (2 * val4 params.modulus) := by
      nlinarith only [hcert, hsum, hbound, hmp]
    exact Nat.lt_of_mul_lt_mul_left hmul
  exact ⟨hout, m, hm, by simpa only [hsum] using hcert⟩

#print axioms raw_product_sum_spec

end UdonVerify.Native
