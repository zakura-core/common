import NativeConstants

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem from_loose_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs : A4)
    (ha : val4 limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.from_loose inst looseInst limbs
      ⦃ out => out.limbs=limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.from_loose
  simp only [
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    bind_ok,Bool.false_eq_true,↓reduceIte]
  step -grind with (from_montgomery_loose_spec inst params limbs ha) as ⟨out,hout⟩
  exact hout

@[step]
theorem from_canonical_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (limbs : A4) (ha : val4 limbs < val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_limbs inst looseInst limbs
      ⦃ out => val4 out.limbs < 2*val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs=val4 limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_limbs
  have hmodulus : inst.MODULUS=ok params.modulus := params.modulus_ok
  rw [hmodulus]
  simp only [bind_ok]
  rw [compare_eq]
  step -grind with (slice_compare_limbs_spec limbs params.modulus) as ⟨order,horder⟩
  have hless : order=Ordering.lt := by
    cases order <;> simp only [orderingRel] at horder ⊢ <;> omega
  subst order
  rw [ordering_is_lt]
  simp only [bind_ok]
  step -grind
  rw [constants.radix2_ok]
  simp only [bind_ok]
  rw [multiply_loose_eq]
  have hr2 : val4 constants.radix2 < val4 params.modulus := by
    rw [constants.radix2_val]
    exact Nat.mod_lt _ params.positive
  step -grind with (montgomery_multiply_loose_spec (kernelInst inst) params limbs constants.radix2
      (by omega) (by omega)) as ⟨product,hbound,m,hm,hcert⟩
  step -grind with (from_loose_loose_spec inst params product hbound) as ⟨out,hout⟩
  refine ⟨by simpa only [hout] using hbound,?_⟩
  unfold decode
  rw [hout]
  have hr2mod : Nat.ModEq (val4 params.modulus) (val4 constants.radix2) (R^2) := by
    unfold Nat.ModEq
    rw [constants.radix2_val,Nat.mod_mod]
  rw [decoded_conversion _ inverse _ _ _ m hinverse hr2mod hcert,Nat.mod_eq_of_lt ha]

@[step]
theorem from_u64_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1) (value : U64) :
    NativeField.zakura_udon.field.pasta.PastaField.from_u64 inst looseInst value
      ⦃ out => val4 out.limbs < 2*val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs=value.val ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.from_u64
  have hvalue : val4 (Array.make 4#usize [value,0#u64,0#u64,0#u64])=value.val := by simp [val4]
  have hbound : val4 (Array.make 4#usize [value,0#u64,0#u64,0#u64]) < val4 params.modulus := by
    rw [hvalue]
    have hp := params.offset_positive
    norm_num only [R,B] at hp
    scalar_tac
  step -grind with (from_canonical_loose_spec inst params constants inverse hinverse
      (Array.make 4#usize [value,0#u64,0#u64,0#u64]) hbound) as ⟨out,hout,hdecode⟩
  exact ⟨hout,by simpa only [hvalue] using hdecode⟩

@[step]
theorem fp_from_u64_spec (value : U64) : NativeField.fp_from_u64 value ⦃ out =>
    val4 out.limbs < 2*fpPrime ∧ decode fpPrime fpRadixInverse out.limbs=value.val ⦄ := by
  unfold NativeField.fp_from_u64
  step -grind with (from_u64_loose_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse value) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fq_from_u64_spec (value : U64) : NativeField.fq_from_u64 value ⦃ out =>
    val4 out.limbs < 2*fqPrime ∧ decode fqPrime fqRadixInverse out.limbs=value.val ⦄ := by
  unfold NativeField.fq_from_u64
  step -grind with (from_u64_loose_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse value) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem from_u128_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1) (value : U128) :
    NativeField.zakura_udon.field.pasta.PastaField.from_u128 inst looseInst value
      ⦃ out => val4 out.limbs < 2*val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs=value.val ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.from_u128
  simp only [lift,bind_ok]
  step -grind with U128.ShiftRight_IScalar_spec as ⟨high,hhigh,hhighb⟩
  have hvalue : val4 (Array.make 4#usize
      [UScalar.cast .U64 value,UScalar.cast .U64 high,0#u64,0#u64])=value.val := by
    simp [val4,UScalar.cast_val_eq,Nat.shiftRight_eq_div_pow,hhigh,U64.numBits]
    change value.val%B+B*(value.val/B%B)=value.val
    have hhi : value.val / B < B := by norm_num only [B]; scalar_tac
    rw [Nat.mod_eq_of_lt hhi]
    exact Nat.mod_add_div value.val B
  have hbound : val4 (Array.make 4#usize
      [UScalar.cast .U64 value,UScalar.cast .U64 high,0#u64,0#u64]) < val4 params.modulus := by
    rw [hvalue]
    have hp := params.offset_positive
    norm_num only [R,B] at hp
    scalar_tac
  step -grind with (from_canonical_loose_spec inst params constants inverse hinverse
      (Array.make 4#usize [UScalar.cast .U64 value,UScalar.cast .U64 high,0#u64,0#u64]) hbound)
      as ⟨out,hout,hdecode⟩
  exact ⟨hout,by simpa only [hvalue] using hdecode⟩

@[step]
theorem fp_from_u128_spec (value : U128) : NativeField.fp_from_u128 value ⦃ out =>
    val4 out.limbs < 2*fpPrime ∧ decode fpPrime fpRadixInverse out.limbs=value.val ⦄ := by
  unfold NativeField.fp_from_u128
  step -grind with (from_u128_loose_spec fpNativeInst fpNativeParameters fpConversionParameters
      fpRadixInverse fp_radix_inverse value) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fq_from_u128_spec (value : U128) : NativeField.fq_from_u128 value ⦃ out =>
    val4 out.limbs < 2*fqPrime ∧ decode fqPrime fqRadixInverse out.limbs=value.val ⦄ := by
  unfold NativeField.fq_from_u128
  step -grind with (from_u128_loose_spec fqNativeInst fqNativeParameters fqConversionParameters
      fqRadixInverse fq_radix_inverse value) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

#print axioms fp_from_u128_spec
#print axioms fq_from_u128_spec
#print axioms fp_from_u64_spec
#print axioms fq_from_u64_spec

end UdonVerify.Native
