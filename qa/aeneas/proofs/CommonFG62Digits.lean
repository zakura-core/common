import CommonFG62Rows
import CommonCancellationWords
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def fgRowDigit (value : I128) : I64 :=
  UScalar.hcast .I64 (IScalar.hcast .U64 value &&& 4611686018427387903#u64)

theorem fg_row_mask_value (value : I128) :
    ((IScalar.hcast .U64 value &&& 4611686018427387903#u64).val : Int) =
      value.val%signedRadix := by
  rw [and_mask_mod _ _ 62 mask62_value,IScalar.hcast_val_eq]
  change (((value.val%(2^64)).toNat % (2^62) : Nat) : Int) = value.val%(2^62)
  rw [Int.natCast_emod,Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  norm_num only [Nat.cast_pow,Nat.cast_ofNat]
  exact Int.emod_emod_of_dvd value.val (by norm_num)

theorem fg_row_digit_value (value : I128) :
    (fgRowDigit value).val=value.val%signedRadix ∧
      0≤(fgRowDigit value).val ∧ (fgRowDigit value).val<signedRadix := by
  have hm := fg_row_mask_value value
  have hn := row_digit_normalized value.val
  have hb : (IScalar.hcast .U64 value &&& 4611686018427387903#u64).val<2^62 := by
    norm_num only [signedRadix] at hm hn
    omega
  have heq : (fgRowDigit value).val=value.val%signedRadix := by
    unfold fgRowDigit
    rw [signed62_cast_value _ hb,hm]
  exact ⟨heq,by rw [heq];exact hn.1,by rw [heq];exact hn.2⟩

theorem fg_row_low_zero (value : I128) (h : value.val%signedRadix=0) :
    IScalar.hcast .U64 value &&& 4611686018427387903#u64=0#u64 := by
  apply UScalar.eq_of_val_eq
  have hm := fg_row_mask_value value
  change (IScalar.hcast .U64 value &&& 4611686018427387903#u64).val=0
  rw [h] at hm
  exact_mod_cast hm

def fgRowTail (value : I128) : Result I64 := do
  let out ← lift (IScalar.cast .I64 value)
  let back ← lift (core.convert.num.FromI128I64.from out)
  massert (value=back)
  ok out

theorem fg_row_tail_value (value : I128) (h : |value.val|≤signedRadix+2) :
    (IScalar.cast .I64 value).val=value.val := by
  have hb := row_carry_i64 value.val h
  apply IScalar.val_mod_pow_inBounds
  · simpa only [IScalarTy.numBits] using hb.1
  · simpa only [IScalarTy.numBits] using hb.2

theorem fg_row_tail_back (value : I128) (h : |value.val|≤signedRadix+2) :
    value=core.convert.num.FromI128I64.from (IScalar.cast .I64 value) := by
  apply IScalar.eq_of_val_eq
  simp only [core.convert.num.FromI128I64.from_val_eq,fg_row_tail_value value h]

@[step]
theorem fg_row_tail_spec (value : I128) (h : |value.val|≤signedRadix+2) :
    fgRowTail value ⦃ out => out.val=value.val ⦄ := by
  have hb := row_carry_i64 value.val h
  have hcast : (IScalar.cast .I64 value).val=value.val := by
    apply IScalar.val_mod_pow_inBounds
    · simpa only [IScalarTy.numBits] using hb.1
    · simpa only [IScalarTy.numBits] using hb.2
  have hback : value=core.convert.num.FromI128I64.from (IScalar.cast .I64 value) := by
    apply IScalar.eq_of_val_eq
    simp only [core.convert.num.FromI128I64.from_val_eq,hcast]
  unfold fgRowTail
  simp only [lift,bind_ok]
  step -grind
  try simp only [WP.spec_ok]
  exact hcast

#print axioms fg_row_mask_value
#print axioms fg_row_digit_value
#print axioms fg_row_low_zero
#print axioms fg_row_tail_value
#print axioms fg_row_tail_back
#print axioms fg_row_tail_spec
end UdonVerify.CommonSigned62
