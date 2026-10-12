import CommonCoeffSpecialMath

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def normalizeDigit (value : I64) : I64 := value &&& 4611686018427387903#i64

theorem normalize_digit_value (value : I64) :
    (normalizeDigit value).val = value.val % signedRadix ∧
      0 ≤ (normalizeDigit value).val ∧ (normalizeDigit value).val < signedRadix := by
  let masked := IScalar.hcast .U64 value &&& 4611686018427387903#u64
  have hm : (masked.val : Int) = value.val % signedRadix := by
    rw [show masked.val = (IScalar.hcast .U64 value).val % 2 ^ 62 from
      and_mask_mod _ _ 62 mask62_value, Int.natCast_emod]
    exact signed_cast_mod62 value
  have hr := row_digit_normalized value.val
  have hb : masked.val < 2 ^ 62 := by norm_num only [signedRadix] at hm hr; omega
  have heq : normalizeDigit value = UScalar.hcast .I64 masked := by
    apply I64.bv_eq_imp_eq
    change value.bv &&& (4611686018427387903#i64).bv =
      ((value.bv.signExtend 64) &&& (4611686018427387903#u64).bv).zeroExtend 64
    simp only [BitVec.signExtend_eq, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq]
    rfl
  rw [heq, signed62_cast_value masked hb, hm]
  exact ⟨rfl, hr⟩

theorem signed_not_value (value : I64) : (~~~value).val = -value.val - 1 := by
  change (~~~value.bv).toInt = -value.bv.toInt - 1
  rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_bmod]
  have hb := value.bv.isLt
  norm_num only at hb ⊢
  simp only [Int.bmod_def]
  omega

theorem xor_sign_mask_value (value control : I64) :
    (value ^^^ signMask control).val = if control.val < 0 then -value.val - 1 else value.val := by
  unfold signMask
  split_ifs
  · have heq : value ^^^ (-1)#i64 = ~~~value := by
      apply I64.bv_eq_imp_eq
      change value.bv ^^^ ((-1)#i64).bv = ~~~value.bv
      rw [show ((-1)#i64).bv = BitVec.allOnes 64 from by decide, BitVec.xor_allOnes]
    rw [heq, signed_not_value]
  · have heq : value ^^^ 0#i64 = value := by
      apply I64.bv_eq_imp_eq
      change value.bv ^^^ (0#i64).bv = value.bv
      rw [show (0#i64).bv = 0#64 from by decide, BitVec.xor_zero]
    rw [heq]

def normalizeNegate (value control : I64) : Result I64 :=
  (value ^^^ signMask control) - signMask control

@[step]
theorem normalize_negate_spec (value control : I64)
    (h : -2 * signedRadix + 2 ≤ value.val ∧ value.val ≤ 2 * signedRadix - 2) :
    normalizeNegate value control ⦃ out =>
      out.val = (if control.val < 0 then -value.val else value.val) ∧
      -2 * signedRadix + 2 ≤ out.val ∧ out.val ≤ 2 * signedRadix - 2 ⦄ := by
  have hx := xor_sign_mask_value value control
  have hs : (signMask control).val = if control.val < 0 then -1 else 0 := by
    unfold signMask
    split_ifs <;> decide
  unfold normalizeNegate
  have hfit : -(2 ^ 63) ≤ (value ^^^ signMask control).val - (signMask control).val ∧
      (value ^^^ signMask control).val - (signMask control).val < 2 ^ 63 := by
    rw [hx, hs]
    split_ifs <;> norm_num only [signedRadix] at h ⊢ <;> omega
  step +scalarTac -grind with I64.sub_spec as ⟨out, hout⟩
  rw [hx, hs] at hout
  split_ifs at hout ⊢ <;> constructor <;> omega

@[step]
theorem normalize_shift_spec (value : I64) :
    value >>> 62#i32 ⦃ out => out.val = value.val / signedRadix ⦄ := by
  step -grind with I64.ShiftRight_IScalar_spec as ⟨out, hout, _⟩
  simpa only [show (62#i32).toNat = 62 from by decide, Int.shiftRight_eq_div_pow,
    signedRadix, Nat.cast_pow, Nat.cast_ofNat] using hout

@[step]
theorem normalize_i64_add_spec (left right : I64) (lo hi : Int)
    (hlo : lo ≤ left.val + right.val) (hhi : left.val + right.val ≤ hi)
    (hfit : -(2 ^ 63) ≤ lo ∧ hi < 2 ^ 63) :
    left + right ⦃ out => out.val = left.val + right.val ∧ lo ≤ out.val ∧ out.val ≤ hi ⦄ := by
  step +scalarTac -grind with I64.add_spec as ⟨out, hout⟩
  exact ⟨hout, by rw [hout]; exact hlo, by rw [hout]; exact hhi⟩

#print axioms normalize_digit_value
#print axioms signed_not_value
#print axioms xor_sign_mask_value
#print axioms normalize_negate_spec
#print axioms normalize_shift_spec
#print axioms normalize_i64_add_spec
end UdonVerify.CommonSigned62
