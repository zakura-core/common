import NativePredicates

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem is_one_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (value : Element M Loose) :
    NativeField.zakura_udon.field.pasta.PastaField.is_one inst looseInst value ⦃ out =>
      out=true ↔ val4 value.limbs=val4 constants.radix ∨
        val4 value.limbs=val4 constants.radix+val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.is_one
  have hm : inst.MODULUS=ok params.modulus := params.modulus_ok
  rw [hm,constants.radix_ok]
  simp only [bind_ok]
  rw [add_limbs_eq]
  step -grind with (slice_add_limbs_spec constants.radix params.modulus)
    as ⟨looseOne,carry,hcarry,hsum⟩
  have hr : val4 constants.radix<val4 params.modulus := by
    rw [constants.radix_val]
    exact Nat.mod_lt _ params.positive
  have hlt : val4 constants.radix+val4 params.modulus<R := by
    have hp := params.thrice_lt
    omega
  have hcarryzero : carry.val=0 := by
    norm_num only [R,B] at hsum hlt
    omega
  have hl : val4 looseOne=val4 constants.radix+val4 params.modulus := by
    simpa [hcarryzero] using hsum
  have hrEq := val4_eq_iff value.limbs constants.radix
  have hlEq := val4_eq_iff value.limbs looseOne
  simp only [looseInst,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    index0_eq,index1_eq,index2_eq,index3_eq,bind_ok,Bool.false_eq_true,↓reduceIte]
  split_ifs <;> simp_all [WP.spec_ok,u64_eq_iff]

theorem decoded_one_iff (p inverse a : Nat) (hp : 1<p)
    (hinverse : Nat.ModEq p (R*inverse) 1) :
    (a*inverse)%p=1 ↔ a%p=R%p := by
  constructor
  · intro h
    have hone : Nat.ModEq p (a*inverse) 1 := by
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt hp] using h
    have hs := hone.mul_left R
    have hi := hinverse.mul_left a
    have hcancel : Nat.ModEq p a R := by
      simpa only [mul_one] using hi.symm.trans (by convert hs using 1 <;> ring)
    exact hcancel
  · intro h
    have hraw : Nat.ModEq p a R := h
    have hs := (hraw.mul_right inverse).trans hinverse
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hp] using hs

theorem loose_mod_representative_iff (p a r : Nat) (hp : 0<p) (hr : r<p) (ha : a<2*p) :
    a%p=r ↔ a=r ∨ a=r+p := by
  have hdecomp := Nat.mod_add_div a p
  have hquot : a/p<2 := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa only [mul_comm] using ha)
  constructor
  · intro h
    have hqnonneg : 0≤a/p := Nat.zero_le _
    have hcases : a/p=0 ∨ a/p=1 := by omega
    rcases hcases with hq|hq <;> simp only [h,hq,mul_zero,mul_one,add_zero] at hdecomp <;> omega
  · rintro (rfl|rfl) <;> simp [Nat.add_mod,Nat.mod_eq_of_lt hr]

@[step]
theorem fp_is_one_spec (value : Element Base Loose) (ha : val4 value.limbs<2*fpPrime) :
    NativeField.fp_is_one value ⦃ out => out=true ↔ decode fpPrime fpRadixInverse value.limbs=1 ⦄ := by
  unfold NativeField.fp_is_one
  step -grind with (is_one_loose_spec fpNativeInst fpNativeParameters
      fpConversionParameters value) as ⟨out,hout⟩
  have hp : 1<fpPrime := by
    have h := fpParameters.offset_positive
    change R/4<fpPrime at h
    norm_num only [R,B] at h
    omega
  have hr : val4 fpConversionParameters.radix<fpPrime := by
    rw [fpConversionParameters.radix_val]
    exact Nat.mod_lt R fpParameters.positive
  have hrval : val4 fpConversionParameters.radix=R%fpPrime := fpConversionParameters.radix_val
  have heq : decode fpPrime fpRadixInverse value.limbs=1 ↔
      val4 value.limbs=val4 fpConversionParameters.radix ∨
      val4 value.limbs=val4 fpConversionParameters.radix+fpPrime := by
    rw [decode,decoded_one_iff fpPrime fpRadixInverse _ hp fp_radix_inverse,←hrval]
    exact loose_mod_representative_iff fpPrime _ _ fpParameters.positive hr ha
  exact hout.trans heq.symm

#print axioms fp_is_one_spec

@[step]
theorem fq_is_one_spec (value : Element Scalar Loose) (ha : val4 value.limbs<2*fqPrime) :
    NativeField.fq_is_one value ⦃ out => out=true ↔ decode fqPrime fqRadixInverse value.limbs=1 ⦄ := by
  unfold NativeField.fq_is_one
  step -grind with (is_one_loose_spec fqNativeInst fqNativeParameters
      fqConversionParameters value) as ⟨out,hout⟩
  have hp : 1<fqPrime := by
    have h := fqParameters.offset_positive
    change R/4<fqPrime at h
    norm_num only [R,B] at h
    omega
  have hr : val4 fqConversionParameters.radix<fqPrime := by
    rw [fqConversionParameters.radix_val]
    exact Nat.mod_lt R fqParameters.positive
  have hrval : val4 fqConversionParameters.radix=R%fqPrime := fqConversionParameters.radix_val
  have heq : decode fqPrime fqRadixInverse value.limbs=1 ↔
      val4 value.limbs=val4 fqConversionParameters.radix ∨
      val4 value.limbs=val4 fqConversionParameters.radix+fqPrime := by
    rw [decode,decoded_one_iff fqPrime fqRadixInverse _ hp fq_radix_inverse,←hrval]
    exact loose_mod_representative_iff fqPrime _ _ fqParameters.positive hr ha
  exact hout.trans heq.symm

#print axioms fq_is_one_spec

end UdonVerify.Native
