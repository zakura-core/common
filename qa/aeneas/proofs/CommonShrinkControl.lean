import CommonShrinkWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def shrinkLengthMask (len : Usize) : Result I64 := do
  let reduced ← UScalar.hcast .I64 len - 2#i64
  reduced >>> 63#i32

@[step]
theorem shrink_length_mask_spec (len : Usize) (hlen : 1 ≤ len.val ∧ len.val ≤ 5) :
    shrinkLengthMask len ⦃ out => out = (if 2 ≤ len.val then 0#i64 else (-1)#i64) ⦄ := by
  have hcast : (UScalar.hcast .I64 len).val = (len.val : Int) := by
    rw [UScalar.hcast_val_eq]
    apply Arith.Int.bmod_pow2_eq_of_inBounds 63 <;> omega
  unfold shrinkLengthMask
  step +scalarTac -grind with I64.sub_spec as ⟨reduced, hval⟩
  rw [hcast] at hval
  step -grind with (signed_sign_mask_spec reduced) as ⟨out, hout⟩
  rw [hout]
  unfold signMask
  by_cases hlarge : 2 ≤ len.val
  · have hnonneg : ¬reduced.val < 0 := by omega
    simp only [if_neg hnonneg, if_pos hlarge]
  · have hnegative : reduced.val < 0 := by omega
    simp only [if_pos hnegative, if_neg hlarge]

def CanShrink62 (len : Nat) (fTop gTop : I64) : Prop :=
  2 ≤ len ∧ (fTop = 0#i64 ∨ fTop = (-1)#i64) ∧ (gTop = 0#i64 ∨ gTop = (-1)#i64)

theorem shrink_condition_iff (len : Nat) (fTop gTop : I64) :
    (((if 2 ≤ len then 0#i64 else (-1)#i64) ||| (fTop ^^^ signMask fTop)) |||
      (gTop ^^^ signMask gTop)) = 0#i64 ↔ CanShrink62 len fTop gTop := by
  rw [signed_or_eq_zero, signed_or_eq_zero, shrink_sign_extension_iff, shrink_sign_extension_iff]
  unfold CanShrink62
  by_cases hl : 2 ≤ len <;> simp [hl]

#print axioms shrink_length_mask_spec
#print axioms shrink_condition_iff
end UdonVerify.CommonSigned62
