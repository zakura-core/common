import CommonSigned62Bounds
import CommonDivstepWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def signMask (value : I64) : I64 := if value.val < 0 then (-1)#i64 else 0#i64

@[step]
theorem signed_sign_mask_spec (value : I64) :
    value >>> 63#i32 ⦃ out => out = signMask value ⦄ := by
  step -grind with I64.ShiftRight_IScalar_spec as ⟨out, hval, _⟩
  have hv : out.val = value.val / (2 ^ 63) := by
    simpa only [show (63#i32).toNat = 63 from by decide, Int.shiftRight_eq_div_pow,
      Nat.cast_pow, Nat.cast_ofNat] using hval
  apply IScalar.eq_of_val_eq
  rw [hv]
  unfold signMask
  split_ifs with hnegative
  · change value.val / (2 ^ 63) = -1
    scalar_tac
  · change value.val / (2 ^ 63) = 0
    scalar_tac

theorem and_sign_mask_eq (value control : I64) :
    value &&& signMask control = if control.val < 0 then value else 0#i64 := by
  unfold signMask
  split_ifs
  · apply I64.bv_eq_imp_eq
    change value.bv &&& ((-1)#i64).bv = value.bv
    rw [show ((-1)#i64).bv = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]
  · apply I64.bv_eq_imp_eq
    change value.bv &&& (0#i64).bv = (0#i64).bv
    rw [show (0#i64).bv = 0#64 from by decide, BitVec.and_zero]

theorem signed62_sign_iff (a : Signed62) (hn : signed62Normalized a) :
    signed62Value a < 0 ↔ a[4]!.val < 0 := by
  have ha : active62Normalized a 5 := by
    intro k hk
    exact hn ⟨k.val, by omega⟩
  simpa only [active62_value_five] using active62_sign_iff a 5 (by decide) ha

def coeffSignStart (u v d4 e4 : I64) : Result I64 := do
  let sd ← d4 >>> 63#i32
  let se ← e4 >>> 63#i32
  (u &&& sd) + (v &&& se)

theorem signed_row_selection_bound (u v : Int) (d e : Prop) [Decidable d] [Decidable e]
    (hrow : |u| + |v| ≤ signedRadix) :
    |(if d then u else 0) + (if e then v else 0)| ≤ signedRadix := by
  have hu : |u| ≤ signedRadix := by have := abs_nonneg v; omega
  have hv : |v| ≤ signedRadix := by have := abs_nonneg u; omega
  have hs := abs_add_le u v
  have hb : 0 ≤ signedRadix := by norm_num [signedRadix]
  split_ifs <;> (try simp only [add_zero, zero_add, abs_zero]) <;> omega

@[step]
theorem coeff_sign_start_spec (u v d4 e4 : I64)
    (hrow : |u.val| + |v.val| ≤ signedRadix) :
    coeffSignStart u v d4 e4 ⦃ out =>
      out.val = (if d4.val < 0 then u.val else 0) + (if e4.val < 0 then v.val else 0) ∧
      |out.val| ≤ signedRadix ⦄ := by
  let left : I64 := if d4.val < 0 then u else 0#i64
  let right : I64 := if e4.val < 0 then v else 0#i64
  have hl : left.val = if d4.val < 0 then u.val else 0 := by
    dsimp only [left]
    split_ifs <;> rfl
  have hr : right.val = if e4.val < 0 then v.val else 0 := by
    dsimp only [right]
    split_ifs <;> rfl
  have hb : |left.val + right.val| ≤ signedRadix := by
    rw [hl, hr]
    exact signed_row_selection_bound u.val v.val (d4.val < 0) (e4.val < 0) hrow
  have hfit := abs_le.mp hb
  norm_num only [signedRadix] at hfit
  unfold coeffSignStart
  step -grind with signed_sign_mask_spec as ⟨sd, hsd⟩
  step -grind with signed_sign_mask_spec as ⟨se, hse⟩
  rw [hsd, hse, and_sign_mask_eq, and_sign_mask_eq]
  step +scalarTac -grind with I64.add_spec as ⟨out, hout⟩
  try simp only [WP.spec_ok]
  have hout' : out.val = left.val + right.val := hout
  exact ⟨by rw [hout', hl, hr], by rw [hout']; exact hb⟩

#print axioms signed_sign_mask_spec
#print axioms and_sign_mask_eq
#print axioms signed62_sign_iff
#print axioms signed_row_selection_bound
#print axioms coeff_sign_start_spec
end UdonVerify.CommonSigned62
