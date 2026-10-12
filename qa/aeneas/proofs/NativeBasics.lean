import NativeArithmetic
import LimbProofs

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev reducedInst :=
  NativeField.zakura_udon.field.pasta.representation.Reduced.Insts.Zakura_udonFieldPastaRepresentationReductionState

theorem decoded_sum (p inverse a b u : Nat) (h : Nat.ModEq p u (a+b)) :
    (u*inverse)%p = ((a*inverse)%p+(b*inverse)%p)%p := by
  have hs := h.mul_right inverse
  rw [add_mul] at hs
  exact Eq.trans hs (Nat.add_mod (a*inverse) (b*inverse) p)

theorem decoded_reduce (p inverse u : Nat) :
    (u%p*inverse)%p = (u*inverse)%p := by
  rw [Nat.mul_mod, Nat.mod_mod]
  exact (Nat.mul_mod u inverse p).symm

@[step]
theorem add_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (lhs : Element M S) (rhs : Element M T)
    (ha : val4 lhs.limbs < 2*val4 params.modulus)
    (hb : val4 rhs.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.add inst lhs rhs ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (val4 out.limbs) (val4 lhs.limbs+val4 rhs.limbs) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.add
  rw [add_twice_eq]
  step -grind with (add_twice_modulus_spec (kernelInst inst) params lhs.limbs rhs.limbs ha hb)
    as ⟨limbs,hvalue,hbound⟩
  step -grind with (from_montgomery_loose_spec inst params limbs hbound) as ⟨out,hout⟩
  refine ⟨by simpa only [hout] using hbound,?_⟩
  have hmod : Nat.ModEq (2*val4 params.modulus) (val4 out.limbs)
      (val4 lhs.limbs+val4 rhs.limbs) := by
    unfold Nat.ModEq
    rw [hout,hvalue,Nat.mod_mod]
  exact hmod.of_dvd (dvd_mul_left (val4 params.modulus) 2)

@[step]
theorem reduce_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M Loose)
    (ha : val4 value.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.reduce inst looseInst value ⦃ out =>
      val4 out.limbs < val4 params.modulus ∧
      val4 out.limbs = val4 value.limbs%val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.reduce
  simp only [
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [reduce_once_eq]
  step -grind with (reduce_once_spec (kernelInst inst) params value.limbs ha)
    as ⟨out,hvalue,hbound⟩
  try simp only [WP.spec_ok]
  exact ⟨hbound,hvalue⟩

@[step]
theorem reduce_reduced_spec {M : Type} (inst : Modulus M) (value : Element M Reduced) :
    NativeField.zakura_udon.field.pasta.PastaField.reduce inst reducedInst value
      ⦃ out => out.limbs=value.limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.reduce
  simp [reducedInst,
    NativeField.zakura_udon.field.pasta.representation.Reduced.Insts.Zakura_udonFieldPastaRepresentationReductionState,
    NativeField.zakura_udon.field.pasta.representation.Reduced.Insts.Zakura_udonFieldPastaRepresentationSealedSealed,
    NativeField.zakura_udon.field.pasta.representation.Reduced.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED]

@[step]
theorem widen_spec {M S : Type} (value : Element M S) :
    NativeField.zakura_udon.field.pasta.PastaField.into_loose value
      ⦃ out => out.limbs=value.limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.into_loose
  simp only [WP.spec_ok]

@[step]
theorem fp_add_spec (lhs rhs : Element Base Loose)
    (ha : val4 lhs.limbs < 2*fpPrime) (hb : val4 rhs.limbs < 2*fpPrime) :
    NativeField.fp_add lhs rhs ⦃ out => val4 out.limbs < 2*fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (decode fpPrime fpRadixInverse lhs.limbs+decode fpPrime fpRadixInverse rhs.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_add
  step -grind with (add_spec fpNativeInst fpNativeParameters lhs rhs ha hb)
    as ⟨out,hbound,hmod⟩
  refine ⟨hbound,?_⟩
  exact decoded_sum fpPrime fpRadixInverse _ _ _ hmod

@[step]
theorem fq_add_spec (lhs rhs : Element Scalar Loose)
    (ha : val4 lhs.limbs < 2*fqPrime) (hb : val4 rhs.limbs < 2*fqPrime) :
    NativeField.fq_add lhs rhs ⦃ out => val4 out.limbs < 2*fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (decode fqPrime fqRadixInverse lhs.limbs+decode fqPrime fqRadixInverse rhs.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_add
  step -grind with (add_spec fqNativeInst fqNativeParameters lhs rhs ha hb)
    as ⟨out,hbound,hmod⟩
  refine ⟨hbound,?_⟩
  exact decoded_sum fqPrime fqRadixInverse _ _ _ hmod

@[step]
theorem fp_reduce_spec (value : Element Base Loose) (ha : val4 value.limbs < 2*fpPrime) :
    NativeField.fp_reduce value ⦃ out => val4 out.limbs < fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs = decode fpPrime fpRadixInverse value.limbs ⦄ := by
  unfold NativeField.fp_reduce
  step -grind with (reduce_loose_spec fpNativeInst fpNativeParameters value ha)
    as ⟨out,hbound,hvalue⟩
  refine ⟨hbound,?_⟩
  change (val4 out.limbs*fpRadixInverse)%fpPrime = (val4 value.limbs*fpRadixInverse)%fpPrime
  rw [hvalue]
  exact decoded_reduce fpPrime fpRadixInverse (val4 value.limbs)

@[step]
theorem fq_reduce_spec (value : Element Scalar Loose) (ha : val4 value.limbs < 2*fqPrime) :
    NativeField.fq_reduce value ⦃ out => val4 out.limbs < fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs = decode fqPrime fqRadixInverse value.limbs ⦄ := by
  unfold NativeField.fq_reduce
  step -grind with (reduce_loose_spec fqNativeInst fqNativeParameters value ha)
    as ⟨out,hbound,hvalue⟩
  refine ⟨hbound,?_⟩
  change (val4 out.limbs*fqRadixInverse)%fqPrime = (val4 value.limbs*fqRadixInverse)%fqPrime
  rw [hvalue]
  exact decoded_reduce fqPrime fqRadixInverse (val4 value.limbs)

@[step]
theorem fp_widen_spec (value : Element Base Reduced) (ha : val4 value.limbs < fpPrime) :
    NativeField.fp_widen value ⦃ out => val4 out.limbs < 2*fpPrime ∧
      out.limbs=value.limbs ⦄ := by
  unfold NativeField.fp_widen
  step -grind with (widen_spec value) as ⟨out,hout⟩
  rw [hout]
  exact ⟨by omega,rfl⟩

@[step]
theorem fq_widen_spec (value : Element Scalar Reduced) (ha : val4 value.limbs < fqPrime) :
    NativeField.fq_widen value ⦃ out => val4 out.limbs < 2*fqPrime ∧
      out.limbs=value.limbs ⦄ := by
  unfold NativeField.fq_widen
  step -grind with (widen_spec value) as ⟨out,hout⟩
  rw [hout]
  exact ⟨by omega,rfl⟩

#print axioms fp_add_spec
#print axioms fq_add_spec
#print axioms fp_reduce_spec
#print axioms fq_reduce_spec
#print axioms fp_widen_spec
#print axioms fq_widen_spec

end UdonVerify.Native
