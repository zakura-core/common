import NativeSubtract

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem mul_add_spec {M S T U : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (lhs : Element M S) (rhs : Element M T) (addend : Element M U)
    (ha : val4 lhs.limbs < 2*val4 params.modulus)
    (hb : val4 rhs.limbs < 2*val4 params.modulus)
    (hc : val4 addend.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.mul_add inst lhs rhs addend ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs =
        (decode (val4 params.modulus) inverse lhs.limbs *
         decode (val4 params.modulus) inverse rhs.limbs +
         decode (val4 params.modulus) inverse addend.limbs)%val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.mul_add
  step -grind with (multiply_spec inst params lhs rhs ha hb) as ⟨product,hprod,m,hm,hcert⟩
  step -grind with (add_spec inst params product addend hprod hc) as ⟨out,hbound,hmod⟩
  refine ⟨hbound,?_⟩
  have hmul := decoded_product (val4 params.modulus) inverse _ _ _ m hinverse hcert
  have hadd := decoded_sum (val4 params.modulus) inverse _ _ _ hmod
  change decode (val4 params.modulus) inverse out.limbs = _ at hadd
  rw [hadd,hmul]
  simpa only [decode] using (Nat.mod_add_mod
    (decode (val4 params.modulus) inverse lhs.limbs *
     decode (val4 params.modulus) inverse rhs.limbs)
    (val4 params.modulus) (decode (val4 params.modulus) inverse addend.limbs))

@[step]
theorem mul_sub_spec {M S T U : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (lhs : Element M S) (rhs : Element M T) (subtrahend : Element M U)
    (ha : val4 lhs.limbs < 2*val4 params.modulus)
    (hb : val4 rhs.limbs < 2*val4 params.modulus)
    (hc : val4 subtrahend.limbs < 2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.mul_sub inst lhs rhs subtrahend ⦃ out =>
      val4 out.limbs < 2*val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs =
        ((decode (val4 params.modulus) inverse lhs.limbs *
          decode (val4 params.modulus) inverse rhs.limbs)%val4 params.modulus +
         val4 params.modulus - decode (val4 params.modulus) inverse subtrahend.limbs)%
          val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.mul_sub
  step -grind with (multiply_spec inst params lhs rhs ha hb) as ⟨product,hprod,m,hm,hcert⟩
  step -grind with (subtract_spec inst params product subtrahend hprod hc) as ⟨out,hbound,hmod⟩
  refine ⟨hbound,?_⟩
  have hmul := decoded_product (val4 params.modulus) inverse _ _ _ m hinverse hcert
  have hsub := decoded_difference (val4 params.modulus) inverse _ _ _ params.positive hmod
  change decode (val4 params.modulus) inverse out.limbs = _ at hsub
  rw [hsub,hmul]
  rfl

@[step]
theorem fp_mul_add_spec (lhs rhs addend : Element Base Loose)
    (ha : val4 lhs.limbs < 2*fpPrime) (hb : val4 rhs.limbs < 2*fpPrime)
    (hc : val4 addend.limbs < 2*fpPrime) :
    NativeField.fp_mul_add lhs rhs addend ⦃ out => val4 out.limbs < 2*fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        (decode fpPrime fpRadixInverse lhs.limbs * decode fpPrime fpRadixInverse rhs.limbs +
         decode fpPrime fpRadixInverse addend.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_mul_add
  step -grind with (mul_add_spec fpNativeInst fpNativeParameters fpRadixInverse fp_radix_inverse
    lhs rhs addend ha hb hc) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fq_mul_add_spec (lhs rhs addend : Element Scalar Loose)
    (ha : val4 lhs.limbs < 2*fqPrime) (hb : val4 rhs.limbs < 2*fqPrime)
    (hc : val4 addend.limbs < 2*fqPrime) :
    NativeField.fq_mul_add lhs rhs addend ⦃ out => val4 out.limbs < 2*fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        (decode fqPrime fqRadixInverse lhs.limbs * decode fqPrime fqRadixInverse rhs.limbs +
         decode fqPrime fqRadixInverse addend.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_mul_add
  step -grind with (mul_add_spec fqNativeInst fqNativeParameters fqRadixInverse fq_radix_inverse
    lhs rhs addend ha hb hc) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fp_mul_sub_spec (lhs rhs subtrahend : Element Base Loose)
    (ha : val4 lhs.limbs < 2*fpPrime) (hb : val4 rhs.limbs < 2*fpPrime)
    (hc : val4 subtrahend.limbs < 2*fpPrime) :
    NativeField.fp_mul_sub lhs rhs subtrahend ⦃ out => val4 out.limbs < 2*fpPrime ∧
      decode fpPrime fpRadixInverse out.limbs =
        ((decode fpPrime fpRadixInverse lhs.limbs * decode fpPrime fpRadixInverse rhs.limbs)%
         fpPrime + fpPrime - decode fpPrime fpRadixInverse subtrahend.limbs)%fpPrime ⦄ := by
  unfold NativeField.fp_mul_sub
  step -grind with (mul_sub_spec fpNativeInst fpNativeParameters fpRadixInverse fp_radix_inverse
    lhs rhs subtrahend ha hb hc) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

@[step]
theorem fq_mul_sub_spec (lhs rhs subtrahend : Element Scalar Loose)
    (ha : val4 lhs.limbs < 2*fqPrime) (hb : val4 rhs.limbs < 2*fqPrime)
    (hc : val4 subtrahend.limbs < 2*fqPrime) :
    NativeField.fq_mul_sub lhs rhs subtrahend ⦃ out => val4 out.limbs < 2*fqPrime ∧
      decode fqPrime fqRadixInverse out.limbs =
        ((decode fqPrime fqRadixInverse lhs.limbs * decode fqPrime fqRadixInverse rhs.limbs)%
         fqPrime + fqPrime - decode fqPrime fqRadixInverse subtrahend.limbs)%fqPrime ⦄ := by
  unfold NativeField.fq_mul_sub
  step -grind with (mul_sub_spec fqNativeInst fqNativeParameters fqRadixInverse fq_radix_inverse
    lhs rhs subtrahend ha hb hc) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

#print axioms fp_mul_add_spec
#print axioms fq_mul_add_spec
#print axioms fp_mul_sub_spec
#print axioms fq_mul_sub_spec
end UdonVerify.Native
