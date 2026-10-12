import NativeConvert
import NativeNegate

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem unsigned_abs_spec (value : I64) :
    NativeField.core.num.I64.unsigned_abs value ⦃ out => out.val=value.val.natAbs ⦄ := by
  unfold NativeField.core.num.I64.unsigned_abs
  split
  · have hnegative : value.val<0 := by scalar_tac
    simp only [bind_ok,WP.spec_ok,IScalar.hcast_val_eq,I64.wrapping_sub_val_eq,
      show (0#i64).val=0 from rfl,IScalarTy.numBits,UScalarTy.numBits]
    norm_num only [Int.zero_sub]
    have hb := Int.bmod_emod (x := -value.val) (m := (18446744073709551616 : Nat))
    norm_num only at hb
    rw [hb]
    rw [Int.emod_eq_of_lt (by omega) (by scalar_tac)]
    have habs := Int.natAbs_of_nonneg (by omega : 0≤-value.val)
    have hnat := Int.toNat_of_nonneg (by omega : 0≤-value.val)
    rw [Int.natAbs_neg] at habs
    omega
  · have hnonnegative : 0≤value.val := by scalar_tac
    simp only [bind_ok,WP.spec_ok,IScalar.hcast_val_eq,UScalarTy.numBits]
    rw [Int.emod_eq_of_lt hnonnegative (by scalar_tac)]
    have habs := Int.natAbs_of_nonneg hnonnegative
    have hnat := Int.toNat_of_nonneg hnonnegative
    omega

@[step]
theorem from_i64_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1) (value : I64) :
    NativeField.zakura_udon.field.pasta.PastaField.from_i64 inst looseInst value ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs =
        if value.val<0 then (val4 params.modulus-value.val.natAbs)%val4 params.modulus
        else value.val.natAbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.from_i64
  step -grind with (unsigned_abs_spec value) as ⟨magnitude,hmagnitude⟩
  step -grind with (from_u64_loose_spec inst params constants inverse hinverse magnitude)
    as ⟨unsigned,hunsigned,hdecode⟩
  split
  · have hnegative : value.val<0 := by scalar_tac
    step -grind with (negate_spec inst params unsigned hunsigned) as ⟨negative,hneg,hmod⟩
    step -grind with (from_loose_loose_spec inst params negative.limbs hneg) as ⟨out,hout⟩
    refine ⟨by simpa only [hout] using hneg,?_⟩
    have hn := decoded_difference (val4 params.modulus) inverse 0
      (val4 unsigned.limbs) (val4 negative.limbs) params.positive hmod
    simp only [zero_mul,Nat.zero_mod,zero_add] at hn
    change decode (val4 params.modulus) inverse negative.limbs =
      (val4 params.modulus-decode (val4 params.modulus) inverse unsigned.limbs)%val4 params.modulus at hn
    rw [hdecode,hmagnitude] at hn
    change decode (val4 params.modulus) inverse out.limbs = _
    simp only [hnegative,↓reduceIte,hout]
    exact hn
  · have hnonnegative : ¬value.val<0 := by scalar_tac
    simp only [WP.spec_ok]
    exact ⟨hunsigned,by simp only [hnonnegative,↓reduceIte,hdecode,hmagnitude]⟩

@[step]
theorem fp_from_i64_spec (value : I64) : NativeField.fp_from_i64 value ⦃ out =>
    val4 out.limbs < 2*fpPrime ∧ decode fpPrime fpRadixInverse out.limbs =
      if value.val<0 then (fpPrime-value.val.natAbs)%fpPrime else value.val.natAbs ⦄ := by
  unfold NativeField.fp_from_i64
  step -grind with (from_i64_loose_spec fpNativeInst fpNativeParameters fpConversionParameters
    fpRadixInverse fp_radix_inverse value) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fq_from_i64_spec (value : I64) : NativeField.fq_from_i64 value ⦃ out =>
    val4 out.limbs < 2*fqPrime ∧ decode fqPrime fqRadixInverse out.limbs =
      if value.val<0 then (fqPrime-value.val.natAbs)%fqPrime else value.val.natAbs ⦄ := by
  unfold NativeField.fq_from_i64
  step -grind with (from_i64_loose_spec fqNativeInst fqNativeParameters fqConversionParameters
    fqRadixInverse fq_radix_inverse value) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

#print axioms unsigned_abs_spec
#print axioms fp_from_i64_spec
#print axioms fq_from_i64_spec
end UdonVerify.Native
