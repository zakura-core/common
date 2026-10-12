import NativeBits

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem decoded_difference (p inverse a b u : Nat) (hp : 0<p)
    (h : Nat.ModEq p (u+b) a) :
    (u*inverse)%p = ((a*inverse)%p+p-(b*inverse)%p)%p := by
  have hs := h.mul_right inverse
  rw [add_mul] at hs
  have hu := Nat.mod_lt (u*inverse) hp
  have hb := Nat.mod_lt (b*inverse) hp
  have hcanon : Nat.ModEq p ((u*inverse)%p+(b*inverse)%p) ((a*inverse)%p) := by
    unfold Nat.ModEq
    rw [Nat.mod_mod,←Nat.add_mod]
    exact hs
  have hadd : (a*inverse)%p+p-(b*inverse)%p+(b*inverse)%p = (a*inverse)%p+p := by omega
  have htarget : Nat.ModEq p ((a*inverse)%p+p-(b*inverse)%p+(b*inverse)%p) ((a*inverse)%p) := by
    rw [hadd]
    simp [Nat.ModEq,Nat.add_mod]
  have hc := Nat.ModEq.add_right_cancel' ((b*inverse)%p) (hcanon.trans htarget.symm)
  rwa [Nat.ModEq,Nat.mod_eq_of_lt hu] at hc

@[step]
theorem subtract_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (lhs : Element M S) (rhs : Element M T)
    (ha : val4 lhs.limbs < 2*val4 params.modulus)
    (hb : val4 rhs.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.sub inst lhs rhs ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (val4 out.limbs+val4 rhs.limbs) (val4 lhs.limbs) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.sub
  rw [sub_twice_eq]
  step -grind with (sub_twice_modulus_spec (kernelInst inst) params lhs.limbs rhs.limbs ha hb)
    as ⟨limbs,hbound,hmod⟩
  step -grind with (from_montgomery_loose_spec inst params limbs hbound) as ⟨out,hout⟩
  refine ⟨by simpa only [hout] using hbound,?_⟩
  rw [hout]
  exact hmod.of_dvd (dvd_mul_left (val4 params.modulus) 2)

@[step]
theorem fp_subtract_spec (lhs rhs : Element Base Loose)
    (ha : val4 lhs.limbs < 2*fpPrime) (hb : val4 rhs.limbs < 2*fpPrime) :
    NativeField.fp_sub lhs rhs ⦃ out => val4 out.limbs < 2*fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (decode fpPrime fpRadixInverse lhs.limbs+fpPrime-decode fpPrime fpRadixInverse rhs.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_sub
  step -grind with (subtract_spec fpNativeInst fpNativeParameters lhs rhs ha hb)
    as ⟨out,hbound,hmod⟩
  refine ⟨hbound,?_⟩
  exact decoded_difference fpPrime fpRadixInverse _ _ _ fpParameters.positive hmod

@[step]
theorem fq_subtract_spec (lhs rhs : Element Scalar Loose)
    (ha : val4 lhs.limbs < 2*fqPrime) (hb : val4 rhs.limbs < 2*fqPrime) :
    NativeField.fq_sub lhs rhs ⦃ out => val4 out.limbs < 2*fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (decode fqPrime fqRadixInverse lhs.limbs+fqPrime-decode fqPrime fqRadixInverse rhs.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_sub
  step -grind with (subtract_spec fqNativeInst fqNativeParameters lhs rhs ha hb)
    as ⟨out,hbound,hmod⟩
  refine ⟨hbound,?_⟩
  exact decoded_difference fqPrime fqRadixInverse _ _ _ fqParameters.positive hmod

#print axioms fp_subtract_spec
#print axioms fq_subtract_spec

end UdonVerify.Native
