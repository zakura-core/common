import NativeConvert

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem reduced_bound_eq {M : Type} (inst : Modulus M) :
    NativeField.zakura_udon.field.pasta.PastaField.BOUND inst reducedInst=inst.MODULUS := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.BOUND
  simp [NativeField.zakura_udon.field.pasta.representation.Reduced.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED]

@[step]
theorem from_montgomery_reduced_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs : A4)
    (ha : val4 limbs < val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.from_montgomery inst reducedInst limbs
      ⦃ out => out.limbs=limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.from_montgomery
  rw [reduced_bound_eq]
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

@[step]
theorem from_loose_reduced_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs : A4)
    (ha : val4 limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.from_loose inst reducedInst limbs ⦃ out =>
      val4 out.limbs < val4 params.modulus ∧ val4 out.limbs=val4 limbs%val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.from_loose
  simp only [NativeField.zakura_udon.field.pasta.representation.Reduced.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    bind_ok,↓reduceIte]
  rw [reduce_once_eq]
  step -grind with (reduce_once_spec (kernelInst inst) params limbs ha) as ⟨canonical,hvalue,hbound⟩
  step -grind with (from_montgomery_reduced_spec inst params canonical hbound) as ⟨out,hout⟩
  exact ⟨by simpa only [hout] using hbound,by simpa only [hout] using hvalue⟩

@[step]
theorem from_canonical_reduced_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (limbs : A4) (ha : val4 limbs < val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_canonical_limbs inst reducedInst limbs
      ⦃ out => val4 out.limbs < val4 params.modulus ∧
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
  step -grind with (from_loose_reduced_spec inst params product hbound) as ⟨out,hcanonical,hout⟩
  refine ⟨hcanonical,?_⟩
  unfold decode
  rw [hout,decoded_reduce]
  have hr2mod : Nat.ModEq (val4 params.modulus) (val4 constants.radix2) (R^2) := by
    unfold Nat.ModEq
    rw [constants.radix2_val,Nat.mod_mod]
  rw [decoded_conversion _ inverse _ _ _ m hinverse hr2mod hcert,Nat.mod_eq_of_lt ha]

@[step]
theorem from_u64_reduced_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1) (value : U64) :
    NativeField.zakura_udon.field.pasta.PastaField.from_u64 inst reducedInst value
      ⦃ out => val4 out.limbs < val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs=value.val ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.from_u64
  have hvalue : val4 (Array.make 4#usize [value,0#u64,0#u64,0#u64])=value.val := by simp [val4]
  have hbound : val4 (Array.make 4#usize [value,0#u64,0#u64,0#u64]) < val4 params.modulus := by
    rw [hvalue]
    have hp := params.offset_positive
    norm_num only [R,B] at hp
    scalar_tac
  step -grind with (from_canonical_reduced_spec inst params constants inverse hinverse
      (Array.make 4#usize [value,0#u64,0#u64,0#u64]) hbound) as ⟨out,hout,hdecode⟩
  exact ⟨hout,by simpa only [hvalue] using hdecode⟩

theorem zero_spec (M S : Type) :
    val4 (NativeField.zakura_udon.field.pasta.PastaField.ZERO M S).limbs=0 := by
  simp [NativeField.zakura_udon.field.pasta.PastaField.ZERO,val4]

@[step]
theorem one_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1) (hp : 1<val4 params.modulus)
    (S : Type) :
    NativeField.zakura_udon.field.pasta.PastaField.ONE S inst ⦃ out =>
      val4 out.limbs < val4 params.modulus ∧ decode (val4 params.modulus) inverse out.limbs=1 ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.ONE
  rw [constants.radix_ok]
  simp only [bind_ok]
  simp only [WP.spec_ok]
  constructor
  · rw [constants.radix_val]
    exact Nat.mod_lt _ params.positive
  · unfold decode
    rw [constants.radix_val,decoded_reduce]
    exact Eq.trans hinverse (Nat.mod_eq_of_lt hp)

@[step]
theorem import_montgomery_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs : A4) (ha : val4 limbs<2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_montgomery_limbs inst looseInst limbs
      ⦃ out => out.limbs=limbs ⦄ := by
  simpa only [NativeField.zakura_udon.field.pasta.encoding.PastaField.from_montgomery_limbs,
    NativeField.zakura_udon.field.pasta.PastaField.from_montgomery] using
    from_montgomery_loose_spec inst params limbs ha

@[step]
theorem montgomery_limbs_spec {M S : Type} (value : Element M S) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.montgomery_limbs value
      ⦃ out => out=value.limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.montgomery_limbs
  simp

@[step]
theorem fp_from_u64_reduced_spec (value : U64) : NativeField.fp_from_u64_reduced value ⦃ out =>
    val4 out.limbs < fpPrime ∧ decode fpPrime fpRadixInverse out.limbs=value.val ⦄ := by
  unfold NativeField.fp_from_u64_reduced
  step -grind with (from_u64_reduced_spec fpNativeInst fpNativeParameters fpConversionParameters
    fpRadixInverse fp_radix_inverse value) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fq_from_u64_reduced_spec (value : U64) : NativeField.fq_from_u64_reduced value ⦃ out =>
    val4 out.limbs < fqPrime ∧ decode fqPrime fqRadixInverse out.limbs=value.val ⦄ := by
  unfold NativeField.fq_from_u64_reduced
  step -grind with (from_u64_reduced_spec fqNativeInst fqNativeParameters fqConversionParameters
    fqRadixInverse fq_radix_inverse value) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fp_reduce_reduced_spec (value : Element Base Reduced) (ha : val4 value.limbs<fpPrime) :
    NativeField.fp_reduce_reduced value ⦃ out => val4 out.limbs<fpPrime ∧ out.limbs=value.limbs ⦄ := by
  unfold NativeField.fp_reduce_reduced
  step -grind with (reduce_reduced_spec fpNativeInst value) as ⟨out,hout⟩
  exact ⟨by simpa only [hout] using ha,hout⟩

@[step]
theorem fq_reduce_reduced_spec (value : Element Scalar Reduced) (ha : val4 value.limbs<fqPrime) :
    NativeField.fq_reduce_reduced value ⦃ out => val4 out.limbs<fqPrime ∧ out.limbs=value.limbs ⦄ := by
  unfold NativeField.fq_reduce_reduced
  step -grind with (reduce_reduced_spec fqNativeInst value) as ⟨out,hout⟩
  exact ⟨by simpa only [hout] using ha,hout⟩

@[step]
theorem fp_zero_spec : NativeField.fp_zero ⦃ out =>
    val4 out.limbs<fpPrime ∧ decode fpPrime fpRadixInverse out.limbs=0 ⦄ := by
  unfold NativeField.fp_zero
  simp only [WP.spec_ok,decode,zero_spec,zero_mul,Nat.zero_mod]
  exact ⟨fpParameters.positive,True.intro⟩

@[step]
theorem fq_zero_spec : NativeField.fq_zero ⦃ out =>
    val4 out.limbs<fqPrime ∧ decode fqPrime fqRadixInverse out.limbs=0 ⦄ := by
  unfold NativeField.fq_zero
  simp only [WP.spec_ok,decode,zero_spec,zero_mul,Nat.zero_mod]
  exact ⟨fqParameters.positive,True.intro⟩

@[step]
theorem fp_one_spec : NativeField.fp_one ⦃ out =>
    val4 out.limbs<fpPrime ∧ decode fpPrime fpRadixInverse out.limbs=1 ⦄ := by
  unfold NativeField.fp_one
  have hp : 1<val4 fpNativeParameters.modulus := by
    have h := fpNativeParameters.offset_positive
    norm_num only [R,B] at h
    omega
  step -grind with (one_spec fpNativeInst fpNativeParameters fpConversionParameters
    fpRadixInverse fp_radix_inverse hp Loose) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fq_one_spec : NativeField.fq_one ⦃ out =>
    val4 out.limbs<fqPrime ∧ decode fqPrime fqRadixInverse out.limbs=1 ⦄ := by
  unfold NativeField.fq_one
  have hp : 1<val4 fqNativeParameters.modulus := by
    have h := fqNativeParameters.offset_positive
    norm_num only [R,B] at h
    omega
  step -grind with (one_spec fqNativeInst fqNativeParameters fqConversionParameters
    fqRadixInverse fq_radix_inverse hp Loose) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fp_import_montgomery_spec (limbs : A4) (ha : val4 limbs<2*fpPrime) :
    NativeField.fp_import_montgomery limbs ⦃ out => val4 out.limbs<2*fpPrime ∧ out.limbs=limbs ⦄ := by
  unfold NativeField.fp_import_montgomery
  step -grind with (import_montgomery_loose_spec fpNativeInst fpNativeParameters limbs ha) as ⟨out,hout⟩
  exact ⟨by simpa only [hout] using ha,hout⟩

@[step]
theorem fq_import_montgomery_spec (limbs : A4) (ha : val4 limbs<2*fqPrime) :
    NativeField.fq_import_montgomery limbs ⦃ out => val4 out.limbs<2*fqPrime ∧ out.limbs=limbs ⦄ := by
  unfold NativeField.fq_import_montgomery
  step -grind with (import_montgomery_loose_spec fqNativeInst fqNativeParameters limbs ha) as ⟨out,hout⟩
  exact ⟨by simpa only [hout] using ha,hout⟩

@[step]
theorem fp_montgomery_spec (value : Element Base Loose) :
    NativeField.fp_montgomery value ⦃ out => out=value.limbs ⦄ := by
  unfold NativeField.fp_montgomery
  step -grind with (montgomery_limbs_spec value) as ⟨out,hout⟩
  exact hout

@[step]
theorem fq_montgomery_spec (value : Element Scalar Loose) :
    NativeField.fq_montgomery value ⦃ out => out=value.limbs ⦄ := by
  unfold NativeField.fq_montgomery
  step -grind with (montgomery_limbs_spec value) as ⟨out,hout⟩
  exact hout

#print axioms fp_from_u64_reduced_spec
#print axioms fq_from_u64_reduced_spec
#print axioms fp_reduce_reduced_spec
#print axioms fq_reduce_reduced_spec
#print axioms fp_zero_spec
#print axioms fq_zero_spec
#print axioms fp_one_spec
#print axioms fq_one_spec
#print axioms fp_import_montgomery_spec
#print axioms fq_import_montgomery_spec
#print axioms fp_montgomery_spec
#print axioms fq_montgomery_spec
end UdonVerify.Native
