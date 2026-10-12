import NativeHalfLoop
import NativeRepresentation
import NativeDouble

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem val4_parity (limbs : A4) : val4 limbs%2=limbs[0]!.val%2 := by
  simp [val4,Nat.add_mod,Nat.mul_mod,B]

theorem half_left (a : U64) : (a.val*2^63)%B=2^63*(a.val%2) := by
  have h := Nat.mul_mod_mul_left (2^63) a.val 2
  change (a.val*2^63)%(2^63*2)=2^63*(a.val%2)
  rw [Nat.mul_comm a.val (2^63)]
  exact h

theorem half_join (a b : U64) :
    (a.val/2) ||| ((b.val*2^63)%B) = a.val/2+2^63*(b.val%2) := by
  rw [half_left,Nat.or_comm]
  have ha : a.val/2<2^63 := by scalar_tac
  exact ((Nat.two_pow_add_eq_or_of_lt (i := 63) ha (b.val%2)).symm).trans (Nat.add_comm _ _)

@[step]
theorem half_spec {M S : Type} (inst : Modulus M)
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (params : PastaParameters (kernelInst inst)) (bound : Nat)
    (hb : bound=val4 params.modulus ∨ bound=2*val4 params.modulus)
    (hpodd : val4 params.modulus%2=1)
    (hctor : ∀ limbs : A4, val4 limbs<bound →
      NativeField.zakura_udon.field.pasta.PastaField.from_montgomery inst state limbs
        ⦃ out => out.limbs=limbs ⦄)
    (value : Element M S) (ha : val4 value.limbs<bound) :
    NativeField.zakura_udon.field.pasta.PastaField.half inst state value ⦃ out =>
      val4 out.limbs<bound ∧
      2*val4 out.limbs=val4 value.limbs+val4 params.modulus*(val4 value.limbs%2) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.half
  step -grind with Array.index_usize_spec as ⟨input0,hinput0⟩
  step -grind with UScalar.and_spec as ⟨parity,hparity,hparityb⟩
  have hparityval : parity.val=val4 value.limbs%2 := by
    simp only [UScalar.val_and] at hparity
    have hand : input0.val &&& 1 = input0.val%2 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod input0.val 1
    change parity.val=input0.val &&& 1 at hparity
    rw [hand,hinput0] at hparity
    simpa [val4_parity] using hparity
  have hparitybound : parity.val≤1 := by
    rw [hparityval]
    have h := Nat.mod_lt (val4 value.limbs) (by decide : 0<2)
    omega
  step -grind with (wrapping_neg_bit_spec parity hparitybound) as ⟨mask,hmask⟩
  have hmodulus : inst.MODULUS=ok params.modulus := params.modulus_ok
  rw [hmodulus]
  simp only [bind_ok]
  rw [show lift (Array.to_slice_mut value.limbs)=
    ok (Array.to_slice_mut value.limbs) from rfl]
  simp only [Array.to_slice_mut, Array.to_slice, core.slice.Slice.iter_mut,
    mutableZipCtor, _root_.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    bind_ok, Std.uncurry_apply_pair]
  have hloop := half_loop_spec mask value.limbs params.modulus
  simp only [Array.to_slice] at hloop
  step -grind with hloop as ⟨carry,z,hcarry,hsum⟩
  let sum := Array.from_slice value.limbs z.fst.slice
  have hmasked : val4 (Array.make 4#usize
      [params.modulus[0]! &&& mask,params.modulus[1]! &&& mask,
       params.modulus[2]! &&& mask,params.modulus[3]! &&& mask])=
      val4 params.modulus*parity.val := by
    by_cases hz : parity.val=0
    · simp only [hz,↓reduceIte] at hmask
      subst mask
      simp [val4,hz]
    · have hone : parity.val=1 := by omega
      simp only [hz,↓reduceIte] at hmask
      subst mask
      simp only [and_full]
      simp [val4,hone]
  rw [hmasked] at hsum
  have haLoose : val4 value.limbs<2*val4 params.modulus := by rcases hb with h|h <;> omega
  have hpsum : val4 params.modulus*parity.val≤val4 params.modulus := by
    simpa using Nat.mul_le_mul_left (val4 params.modulus) hparitybound
  have hcarryzero : carry.val=0 := by
    have hR := params.thrice_lt
    norm_num only [R,B] at hR hsum
    omega
  have hcarryeq : carry=0#u64 := by scalar_tac
  have hsumval : val4 sum=val4 value.limbs+val4 params.modulus*(val4 value.limbs%2) := by
    simpa only [hcarryzero,hparityval,mul_zero,add_zero] using hsum
  have heven : val4 sum%2=0 := by
    rw [hsumval,Nat.add_mod,Nat.mul_mod,hpodd]
    have hrem := Nat.mod_lt (val4 value.limbs) (by decide : 0<2)
    rcases (by omega : val4 value.limbs%2=0 ∨ val4 value.limbs%2=1) with h|h <;> simp [h]
  step -grind
  step -grind with Array.index_usize_spec as ⟨a0,ha0⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨s0,hs0,hs0b⟩
  step -grind with Array.index_usize_spec as ⟨a1,ha1⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨l1,hl1,hl1b⟩
  step -grind with UScalar.or_spec as ⟨r0,hr0,hr0b⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨s1,hs1,hs1b⟩
  step -grind with Array.index_usize_spec as ⟨a2,ha2⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨l2,hl2,hl2b⟩
  step -grind with UScalar.or_spec as ⟨r1,hr1,hr1b⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨s2,hs2,hs2b⟩
  step -grind with Array.index_usize_spec as ⟨a3,ha3⟩
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨l3,hl3,hl3b⟩
  step -grind with UScalar.or_spec as ⟨r2,hr2,hr2b⟩
  step -grind with U64.ShiftRight_IScalar_spec as ⟨r3,hr3,hr3b⟩
  have hd0 := Nat.mod_add_div a0.val 2
  have hd1 := Nat.mod_add_div a1.val 2
  have hd2 := Nat.mod_add_div a2.val 2
  have hd3 := Nat.mod_add_div a3.val 2
  have hr0val : r0.val=a0.val/2+2^63*(a1.val%2) := by
    simp only [UScalar.val_or,hs0,hl1,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow] at hr0
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits] at hr0
    exact hr0.trans (half_join a0 a1)
  have hr1val : r1.val=a1.val/2+2^63*(a2.val%2) := by
    simp only [UScalar.val_or,hs1,hl2,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow] at hr1
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits] at hr1
    exact hr1.trans (half_join a1 a2)
  have hr2val : r2.val=a2.val/2+2^63*(a3.val%2) := by
    simp only [UScalar.val_or,hs2,hl3,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow] at hr2
    norm_num only [U64.size,U64.numBits,UScalarTy.numBits] at hr2
    exact hr2.trans (half_join a2 a3)
  have hr3val : r3.val=a3.val/2 := by simpa only [Nat.shiftRight_eq_div_pow] using hr3
  have htotal : 2*val4 (Array.make 4#usize [r0,r1,r2,r3])=val4 sum := by
    have hsumparity : a0.val%2=0 := by
      have hp : sum[0]!.val%2=0 := by rw [←val4_parity]; exact heven
      simpa [ha0] using hp
    rw [hsumparity] at hd0
    simp [val4,sum,hr0val,hr1val,hr2val,hr3val,←ha0,←ha1,←ha2,←ha3]
    norm_num [B] at hd0 hd1 hd2 hd3 ⊢
    linear_combination hd0+B*hd1+B^2*hd2+B^3*hd3
  have hcert := htotal.trans hsumval
  have hadded : val4 params.modulus*(val4 value.limbs%2)≤val4 params.modulus := by
    simpa only [hparityval] using hpsum
  have hbound : val4 (Array.make 4#usize [r0,r1,r2,r3])<bound := by
    rcases hb with h|h <;> omega
  step -grind with (hctor (Array.make 4#usize [r0,r1,r2,r3]) hbound) as ⟨out,hout⟩
  exact ⟨by simpa only [hout] using hbound,by simpa only [hout] using htotal.trans hsumval⟩

theorem decoded_half (p inverse halfInverse a u parity : Nat)
    (hinverse : Nat.ModEq p (2*halfInverse) 1) (hcert : 2*u=a+p*parity) :
    (u*inverse)%p = (((a*inverse)%p)*halfInverse)%p := by
  have hmod : Nat.ModEq p (2*u) a := by
    rw [hcert]
    simp [Nat.ModEq,Nat.add_mod]
  have hscaled : Nat.ModEq p ((2*halfInverse)*(u*inverse)) ((a*inverse)*halfInverse) := by
    convert hmod.mul_right (inverse*halfInverse) using 1 <;> ring
  have hcancel : Nat.ModEq p ((2*halfInverse)*(u*inverse)) (u*inverse) := by
    simpa only [one_mul] using hinverse.mul_right (u*inverse)
  have hresult := hcancel.symm.trans hscaled
  calc (u*inverse)%p = ((a*inverse)*halfInverse)%p := hresult
       _ = (((a*inverse)%p)*halfInverse)%p := by simp only [Nat.mul_mod,Nat.mod_mod]


def fpHalfInverse : Nat := (fpPrime+1)/2

theorem fp_modulus_odd : fpPrime%2=1 := by
  norm_num [fpPrime,fpParameters,val4,B,udon_kernel_slice.field.pasta.PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]

theorem fp_half_inverse : Nat.ModEq fpPrime (2*fpHalfInverse) 1 := by
  norm_num [Nat.ModEq,fpHalfInverse,fpPrime,fpParameters,val4,B,udon_kernel_slice.field.pasta.PallasBase.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]


@[step]
theorem fp_half_loose_spec (value : Element Base Loose) (ha : val4 value.limbs<2*fpPrime) :
    NativeField.zakura_udon.field.pasta.PastaField.half fpNativeInst looseInst value
      ⦃ out => val4 out.limbs<2*fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs =
          (decode fpPrime fpRadixInverse value.limbs*fpHalfInverse)%fpPrime ⦄ := by
  step -grind with (half_spec fpNativeInst looseInst fpNativeParameters (2*fpPrime)
    (Or.inr rfl) fp_modulus_odd
    (fun limbs h => from_montgomery_loose_spec fpNativeInst fpNativeParameters limbs h)
    value ha) as ⟨out,hbound,hcert⟩
  exact ⟨hbound,decoded_half fpPrime fpRadixInverse fpHalfInverse _ _ _ fp_half_inverse hcert⟩

#print axioms fp_half_loose_spec


@[step]
theorem fp_half_reduced_spec (value : Element Base Reduced) (ha : val4 value.limbs<fpPrime) :
    NativeField.zakura_udon.field.pasta.PastaField.half fpNativeInst reducedInst value
      ⦃ out => val4 out.limbs<fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs =
          (decode fpPrime fpRadixInverse value.limbs*fpHalfInverse)%fpPrime ⦄ := by
  step -grind with (half_spec fpNativeInst reducedInst fpNativeParameters (fpPrime)
    (Or.inl rfl) fp_modulus_odd
    (fun limbs h => from_montgomery_reduced_spec fpNativeInst fpNativeParameters limbs h)
    value ha) as ⟨out,hbound,hcert⟩
  exact ⟨hbound,decoded_half fpPrime fpRadixInverse fpHalfInverse _ _ _ fp_half_inverse hcert⟩

#print axioms fp_half_reduced_spec


def fqHalfInverse : Nat := (fqPrime+1)/2

theorem fq_modulus_odd : fqPrime%2=1 := by
  norm_num [fqPrime,fqParameters,val4,B,udon_kernel_slice.field.pasta.PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]

theorem fq_half_inverse : Nat.ModEq fqPrime (2*fqHalfInverse) 1 := by
  norm_num [Nat.ModEq,fqHalfInverse,fqPrime,fqParameters,val4,B,udon_kernel_slice.field.pasta.PallasScalar.Insts.Udon_kernel_sliceFieldPastaPrimeModulus.MODULUS]


@[step]
theorem fq_half_loose_spec (value : Element Scalar Loose) (ha : val4 value.limbs<2*fqPrime) :
    NativeField.zakura_udon.field.pasta.PastaField.half fqNativeInst looseInst value
      ⦃ out => val4 out.limbs<2*fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs =
          (decode fqPrime fqRadixInverse value.limbs*fqHalfInverse)%fqPrime ⦄ := by
  step -grind with (half_spec fqNativeInst looseInst fqNativeParameters (2*fqPrime)
    (Or.inr rfl) fq_modulus_odd
    (fun limbs h => from_montgomery_loose_spec fqNativeInst fqNativeParameters limbs h)
    value ha) as ⟨out,hbound,hcert⟩
  exact ⟨hbound,decoded_half fqPrime fqRadixInverse fqHalfInverse _ _ _ fq_half_inverse hcert⟩

#print axioms fq_half_loose_spec


@[step]
theorem fq_half_reduced_spec (value : Element Scalar Reduced) (ha : val4 value.limbs<fqPrime) :
    NativeField.zakura_udon.field.pasta.PastaField.half fqNativeInst reducedInst value
      ⦃ out => val4 out.limbs<fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs =
          (decode fqPrime fqRadixInverse value.limbs*fqHalfInverse)%fqPrime ⦄ := by
  step -grind with (half_spec fqNativeInst reducedInst fqNativeParameters (fqPrime)
    (Or.inl rfl) fq_modulus_odd
    (fun limbs h => from_montgomery_reduced_spec fqNativeInst fqNativeParameters limbs h)
    value ha) as ⟨out,hbound,hcert⟩
  exact ⟨hbound,decoded_half fqPrime fqRadixInverse fqHalfInverse _ _ _ fq_half_inverse hcert⟩

#print axioms fq_half_reduced_spec

#print axioms half_spec
end UdonVerify.Native
