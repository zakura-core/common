import NativeBridge

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev looseInst :=
  NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState

theorem loose_bound_eq {M : Type} (inst : Modulus M) :
    NativeField.zakura_udon.field.pasta.PastaField.BOUND inst looseInst =
      inst.sealedParametersInst.TWICE_MODULUS := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.BOUND
  simp [NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED]

theorem ordering_is_lt :
    NativeField.core.cmp.Ordering.is_lt Ordering.lt = ok true := by
  rfl

@[step]
theorem from_montgomery_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (limbs : A4)
    (hbound : val4 limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.from_montgomery inst looseInst limbs
      ⦃ out => out.limbs = limbs ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.from_montgomery
  rw [loose_bound_eq]
  have htwice : inst.sealedParametersInst.TWICE_MODULUS = ok params.twice := params.twice_ok
  rw [htwice]
  simp only [bind_ok]
  rw [compare_eq]
  step -grind with (slice_compare_limbs_spec limbs params.twice) as ⟨order,horder⟩
  have hless : order = Ordering.lt := by
    have htw := params.twice_val
    cases order <;> simp only [orderingRel] at horder ⊢ <;> omega
  subst order
  rw [ordering_is_lt]
  simp only [bind_ok]
  step

@[step]
theorem multiply_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (lhs : Element M S) (rhs : Element M T)
    (ha : val4 lhs.limbs < 2*val4 params.modulus)
    (hb : val4 rhs.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.mul inst lhs rhs ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      ∃ m : Nat,m < R ∧ R*val4 out.limbs=val4 lhs.limbs*val4 rhs.limbs+m*val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.mul
  rw [multiply_loose_eq]
  step -grind with (montgomery_multiply_loose_spec (kernelInst inst) params lhs.limbs rhs.limbs ha hb)
    as ⟨limbs,hbound,m,hm,hcert⟩
  step -grind with (from_montgomery_loose_spec inst params limbs hbound) as ⟨out,hout⟩
  exact ⟨by simpa [hout] using hbound,m,hm,by simpa [hout] using hcert⟩

@[step]
theorem square_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M S)
    (ha : val4 value.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.square inst value ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      ∃ m : Nat, m < R ∧ R*val4 out.limbs=val4 value.limbs^2+m*val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.square
  rw [square_eq]
  step -grind with (montgomery_square_spec (kernelInst inst) params value.limbs ha)
    as ⟨limbs,hbound,m,hm,hcert⟩
  step -grind with (from_montgomery_loose_spec inst params limbs hbound) as ⟨out,hout⟩
  exact ⟨by simpa [hout] using hbound,m,hm,by simpa [hout] using hcert⟩

def fpPrime : Nat := val4 fpParameters.modulus
def fqPrime : Nat := val4 fqParameters.modulus

def fpRadixInverse : Nat :=
  15353493766103302224812374511606760489073247795810767472367693728416386214313
def fqRadixInverse : Nat :=
  14238205147845459960272226733876560297615832660064601289232577236146637664127

theorem fp_radix_inverse : Nat.ModEq fpPrime (R*fpRadixInverse) 1 := by
  norm_num [Nat.ModEq,fpPrime,fpRadixInverse,fpParameters,val4,R,B,
    udon_kernel_slice.field.pasta.PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]

theorem fq_radix_inverse : Nat.ModEq fqPrime (R*fqRadixInverse) 1 := by
  norm_num [Nat.ModEq,fqPrime,fqRadixInverse,fqParameters,val4,R,B,
    udon_kernel_slice.field.pasta.PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]

def decode (p inverse : Nat) (limbs : A4) : Nat := (val4 limbs*inverse)%p

theorem decoded_product (p inverse a b u m : Nat)
    (hinverse : Nat.ModEq p (R*inverse) 1)
    (hcert : R*u=a*b+m*p) :
    (u*inverse)%p = (((a*inverse)%p)*((b*inverse)%p))%p := by
  have hcertmod := certificate_congruence p (a*b) m u hcert
  have hscaled : Nat.ModEq p ((R*inverse)*(u*inverse)) ((a*inverse)*(b*inverse)) := by
    convert hcertmod.mul (Nat.ModEq.refl (inverse*inverse)) using 1 <;> ring
  have hcancel : Nat.ModEq p ((R*inverse)*(u*inverse)) (u*inverse) := by
    simpa only [one_mul] using hinverse.mul_right (u*inverse)
  have h := hcancel.symm.trans hscaled
  exact Eq.trans h (Nat.mul_mod (a*inverse) (b*inverse) p)

@[step]
theorem fp_multiply_spec (lhs rhs : Element Base Loose)
    (ha : val4 lhs.limbs < 2*fpPrime) (hb : val4 rhs.limbs < 2*fpPrime) :
    NativeField.fp_mul lhs rhs ⦃ out => val4 out.limbs < 2*fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (decode fpPrime fpRadixInverse lhs.limbs*decode fpPrime fpRadixInverse rhs.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_mul
  step -grind with (multiply_spec fpNativeInst fpNativeParameters lhs rhs ha hb)
    as ⟨out,hbound,m,hm,hcert⟩
  refine ⟨hbound,?_⟩
  exact decoded_product fpPrime fpRadixInverse (val4 lhs.limbs) (val4 rhs.limbs)
    (val4 out.limbs) m fp_radix_inverse hcert

@[step]
theorem fq_multiply_spec (lhs rhs : Element Scalar Loose)
    (ha : val4 lhs.limbs < 2*fqPrime) (hb : val4 rhs.limbs < 2*fqPrime) :
    NativeField.fq_mul lhs rhs ⦃ out => val4 out.limbs < 2*fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (decode fqPrime fqRadixInverse lhs.limbs*decode fqPrime fqRadixInverse rhs.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_mul
  step -grind with (multiply_spec fqNativeInst fqNativeParameters lhs rhs ha hb)
    as ⟨out,hbound,m,hm,hcert⟩
  refine ⟨hbound,?_⟩
  exact decoded_product fqPrime fqRadixInverse (val4 lhs.limbs) (val4 rhs.limbs)
    (val4 out.limbs) m fq_radix_inverse hcert

#print axioms fp_multiply_spec
#print axioms fq_multiply_spec

@[step]
theorem fp_square_spec (value : Element Base Loose)
    (ha : val4 value.limbs < 2*fpPrime) :
    NativeField.fp_square value ⦃ out => val4 out.limbs < 2*fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (decode fpPrime fpRadixInverse value.limbs)^2%fpPrime ⦄ := by
  unfold NativeField.fp_square
  step -grind with (square_spec fpNativeInst fpNativeParameters value ha)
    as ⟨out,hbound,m,hm,hcert⟩
  refine ⟨hbound,?_⟩
  simpa only [pow_two, decode] using decoded_product fpPrime fpRadixInverse
    (val4 value.limbs) (val4 value.limbs) (val4 out.limbs) m fp_radix_inverse
    (by simpa only [pow_two, fpPrime, fpNativeParameters, transferParameters] using hcert)

@[step]
theorem fq_square_spec (value : Element Scalar Loose)
    (ha : val4 value.limbs < 2*fqPrime) :
    NativeField.fq_square value ⦃ out => val4 out.limbs < 2*fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (decode fqPrime fqRadixInverse value.limbs)^2%fqPrime ⦄ := by
  unfold NativeField.fq_square
  step -grind with (square_spec fqNativeInst fqNativeParameters value ha)
    as ⟨out,hbound,m,hm,hcert⟩
  refine ⟨hbound,?_⟩
  simpa only [pow_two, decode] using decoded_product fqPrime fqRadixInverse
    (val4 value.limbs) (val4 value.limbs) (val4 out.limbs) m fq_radix_inverse
    (by simpa only [pow_two, fqPrime, fqNativeParameters, transferParameters] using hcert)

#print axioms fp_square_spec
#print axioms fq_square_spec

end UdonVerify.Native
