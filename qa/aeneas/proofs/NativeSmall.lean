import NativeSmallReduction
open Aeneas Std Result
namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem small_multiply_spec {M : Type} (K : U64) (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs : A4)
    (hk0 : 0<K.val) (hk8 : K.val≤8) (ha : val4 limbs<2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.small.multiply K inst limbs ⦃ out =>
      val4 out.limbs<val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (val4 out.limbs) (K.val*val4 limbs) ⦄ := by
  obtain ⟨a0,a1,a2,a3,heq⟩ : ∃ a0 a1 a2 a3 : U64,
      limbs=Array.make 4#usize [a0,a1,a2,a3] :=
    ⟨limbs[0]!,limbs[1]!,limbs[2]!,limbs[3]!,CommonVerify.array_four_eta limbs⟩
  subst limbs
  rw [small_prefix K inst a0 a1 a2 a3 hk0 hk8]
  rw [mac_eq]
  step -grind with slice_mac_identity as ⟨r0,c0,h0⟩
  rw [mac_eq]
  step -grind with slice_mac_identity as ⟨r1,c1,h1⟩
  rw [mac_eq]
  step -grind with slice_mac_identity as ⟨r2,c2,h2⟩
  rw [mac_eq]
  step -grind with slice_mac_identity as ⟨r3,c3,h3⟩
  have hp : val4 (Array.make 4#usize [r0,r1,r2,r3])+R*c3.val=
      K.val*val4 (Array.make 4#usize [a0,a1,a2,a3]) := by
    simp [val4] at *
    unfold R
    linear_combination h0+B*h1+B^2*h2+B^3*h3
  step -grind with (small_finish_spec K inst params
    (Array.make 4#usize [a0,a1,a2,a3]) (Array.make 4#usize [r0,r1,r2,r3])
    c3 hk0 hk8 ha hp) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,hmod⟩

@[step]
theorem fp_triple_spec (value : Element Base Loose) (ha : val4 value.limbs<2*fpPrime) :
    NativeField.fp_triple value ⦃ out => val4 out.limbs<fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (3*decode fpPrime fpRadixInverse value.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_triple NativeField.zakura_udon.field.pasta.PastaField.triple
  step -grind with (small_multiply_spec 3#u64 fpNativeInst fpNativeParameters value.limbs
    (by decide) (by decide) ha) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,decoded_scale fpPrime fpRadixInverse _ _ 3 hmod⟩

#print axioms fp_triple_spec


@[step]
theorem fp_mul_by_4_spec (value : Element Base Loose) (ha : val4 value.limbs<2*fpPrime) :
    NativeField.fp_mul_by_4 value ⦃ out => val4 out.limbs<fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (4*decode fpPrime fpRadixInverse value.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_mul_by_4 NativeField.zakura_udon.field.pasta.PastaField.mul_by_4
  step -grind with (small_multiply_spec 4#u64 fpNativeInst fpNativeParameters value.limbs
    (by decide) (by decide) ha) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,decoded_scale fpPrime fpRadixInverse _ _ 4 hmod⟩

#print axioms fp_mul_by_4_spec


@[step]
theorem fp_mul_by_8_spec (value : Element Base Loose) (ha : val4 value.limbs<2*fpPrime) :
    NativeField.fp_mul_by_8 value ⦃ out => val4 out.limbs<fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (8*decode fpPrime fpRadixInverse value.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_mul_by_8 NativeField.zakura_udon.field.pasta.PastaField.mul_by_8
  step -grind with (small_multiply_spec 8#u64 fpNativeInst fpNativeParameters value.limbs
    (by decide) (by decide) ha) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,decoded_scale fpPrime fpRadixInverse _ _ 8 hmod⟩

#print axioms fp_mul_by_8_spec


@[step]
theorem fq_triple_spec (value : Element Scalar Loose) (ha : val4 value.limbs<2*fqPrime) :
    NativeField.fq_triple value ⦃ out => val4 out.limbs<fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (3*decode fqPrime fqRadixInverse value.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_triple NativeField.zakura_udon.field.pasta.PastaField.triple
  step -grind with (small_multiply_spec 3#u64 fqNativeInst fqNativeParameters value.limbs
    (by decide) (by decide) ha) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,decoded_scale fqPrime fqRadixInverse _ _ 3 hmod⟩

#print axioms fq_triple_spec


@[step]
theorem fq_mul_by_4_spec (value : Element Scalar Loose) (ha : val4 value.limbs<2*fqPrime) :
    NativeField.fq_mul_by_4 value ⦃ out => val4 out.limbs<fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (4*decode fqPrime fqRadixInverse value.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_mul_by_4 NativeField.zakura_udon.field.pasta.PastaField.mul_by_4
  step -grind with (small_multiply_spec 4#u64 fqNativeInst fqNativeParameters value.limbs
    (by decide) (by decide) ha) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,decoded_scale fqPrime fqRadixInverse _ _ 4 hmod⟩

#print axioms fq_mul_by_4_spec


@[step]
theorem fq_mul_by_8_spec (value : Element Scalar Loose) (ha : val4 value.limbs<2*fqPrime) :
    NativeField.fq_mul_by_8 value ⦃ out => val4 out.limbs<fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (8*decode fqPrime fqRadixInverse value.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_mul_by_8 NativeField.zakura_udon.field.pasta.PastaField.mul_by_8
  step -grind with (small_multiply_spec 8#u64 fqNativeInst fqNativeParameters value.limbs
    (by decide) (by decide) ha) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,decoded_scale fqPrime fqRadixInverse _ _ 8 hmod⟩

#print axioms fq_mul_by_8_spec

#print axioms small_multiply_spec
end UdonVerify.Native
