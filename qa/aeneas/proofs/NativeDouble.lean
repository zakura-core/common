import NativeBits
import NativeBasics

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem double_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M S)
    (ha : val4 value.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.double inst value ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (val4 out.limbs) (2*val4 value.limbs) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.double
  step -grind with Array.index_usize_spec as ⟨a0,ha0⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨r0,hr0,hr0b⟩
  step -grind with Array.index_usize_spec as ⟨a1,ha1⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨l1,hl1,hl1b⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨c0,hc0,hc0b⟩
  step -grind with UScalar.or_spec as ⟨r1,hr1,hr1b⟩
  step -grind with Array.index_usize_spec as ⟨a2,ha2⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨l2,hl2,hl2b⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨c1,hc1,hc1b⟩
  step -grind with UScalar.or_spec as ⟨r2,hr2,hr2b⟩
  step -grind with Array.index_usize_spec as ⟨a3,ha3⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨l3,hl3,hl3b⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨c2,hc2,hc2b⟩
  step -grind with UScalar.or_spec as ⟨r3,hr3,hr3b⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry,hcarry,hcarryb⟩
  have hd0 := double_split a0
  have hd1 := double_split a1
  have hd2 := double_split a2
  have hd3 := double_split a3
  have hj1 := double_join a1 a0
  have hj2 := double_join a2 a1
  have hj3 := double_join a3 a2
  have htotal :
      val4 (Array.make 4#usize [r0,r1,r2,r3])+R*carry.val = 2*val4 value.limbs := by
    simp_all [val4,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,U64.size,U64.numBits]
    norm_num [B,R] at *
    simp_all only [hj1,hj2,hj3]
    ring_nf at *
    omega
  have hbound :
      val4 (Array.make 4#usize [r0,r1,r2,r3])+R*carry.val < 4*val4 params.modulus := by
    rw [htotal]
    omega
  rw [reduce_twice_eq]
  step -grind with (reduce_twice_modulus_spec (kernelInst inst) params
      (Array.make 4#usize [r0,r1,r2,r3]) carry hbound) as ⟨limbs,hvalue,hloose⟩
  step -grind with (from_montgomery_loose_spec inst params limbs hloose) as ⟨out,hout⟩
  refine ⟨by simpa only [hout] using hloose,?_⟩
  have hmod : Nat.ModEq (2*val4 params.modulus) (val4 out.limbs) (2*val4 value.limbs) := by
    unfold Nat.ModEq
    rw [hout,hvalue,htotal,Nat.mod_mod]
  exact hmod.of_dvd (dvd_mul_left (val4 params.modulus) 2)

theorem decoded_scale (p inverse a u k : Nat) (h : Nat.ModEq p u (k*a)) :
    (u*inverse)%p = (k*((a*inverse)%p))%p := by
  have hs := h.mul_right inverse
  have hright : ((k*a)*inverse)%p = (k*((a*inverse)%p))%p := by
    rw [mul_assoc, Nat.mul_mod, Nat.mul_mod k ((a*inverse)%p) p, Nat.mod_mod]
  exact Eq.trans hs hright

@[step]
theorem fp_double_spec (value : Element Base Loose) (ha : val4 value.limbs < 2*fpPrime) :
    NativeField.fp_double value ⦃ out => val4 out.limbs < 2*fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (2*decode fpPrime fpRadixInverse value.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_double
  step -grind with (double_spec fpNativeInst fpNativeParameters value ha) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,decoded_scale fpPrime fpRadixInverse _ _ 2 hmod⟩

@[step]
theorem fq_double_spec (value : Element Scalar Loose) (ha : val4 value.limbs < 2*fqPrime) :
    NativeField.fq_double value ⦃ out => val4 out.limbs < 2*fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (2*decode fqPrime fqRadixInverse value.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_double
  step -grind with (double_spec fqNativeInst fqNativeParameters value ha) as ⟨out,hbound,hmod⟩
  exact ⟨hbound,decoded_scale fqPrime fqRadixInverse _ _ 2 hmod⟩

#print axioms double_spec
#print axioms fp_double_spec
#print axioms fq_double_spec

end UdonVerify.Native
