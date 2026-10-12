import NativeConstants
import NativeBits
import Mathlib.Data.Nat.Digits.Defs

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem val4_eq_iff (lhs rhs : A4) : val4 lhs=val4 rhs ↔
    lhs[0]! = rhs[0]! ∧ lhs[1]! = rhs[1]! ∧ lhs[2]! = rhs[2]! ∧ lhs[3]! = rhs[3]! := by
  constructor
  · intro h
    have hdigits (a : A4) : Nat.ofDigits B
        [a[0]!.val,a[1]!.val,a[2]!.val,a[3]!.val]=val4 a := by
      simp only [Nat.ofDigits_cons,Nat.ofDigits_nil,mul_zero,add_zero,val4]
      ring
    have hbounded (a : A4) : ∀ d ∈
        [a[0]!.val,a[1]!.val,a[2]!.val,a[3]!.val], d < B := by
      intro d hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> norm_num only [B] <;> scalar_tac
    have heq := Nat.ofDigits_inj_of_len_eq (by norm_num [B]) (by rfl)
      (hbounded lhs) (hbounded rhs) ((hdigits lhs).trans (h.trans (hdigits rhs).symm))
    simp only [List.cons.injEq] at heq
    exact ⟨UScalar.eq_of_val_eq heq.1,UScalar.eq_of_val_eq heq.2.1,
      UScalar.eq_of_val_eq heq.2.2.1,UScalar.eq_of_val_eq heq.2.2.2.1⟩
  · rintro ⟨h0,h1,h2,h3⟩
    simp only [val4,h0,h1,h2,h3]

theorem index0_eq (a : A4) : Array.index_usize a 0#usize=ok a[0]! := by
  simp [Array.index_usize]
theorem index1_eq (a : A4) : Array.index_usize a 1#usize=ok a[1]! := by
  simp [Array.index_usize]
theorem index2_eq (a : A4) : Array.index_usize a 2#usize=ok a[2]! := by
  simp [Array.index_usize]
theorem index3_eq (a : A4) : Array.index_usize a 3#usize=ok a[3]! := by
  simp [Array.index_usize]

theorem u64_eq_iff (lhs rhs : U64) : lhs=rhs ↔ lhs.val=rhs.val := by
  exact ⟨congrArg UScalar.val, UScalar.eq_of_val_eq⟩

@[step]
theorem is_zero_loose_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (value : Element M Loose) :
    NativeField.zakura_udon.field.pasta.PastaField.is_zero inst looseInst value ⦃ out =>
      out=true ↔ val4 value.limbs=0 ∨ val4 value.limbs=val4 params.modulus ⦄ := by
  have hz := val4_zero_iff value.limbs
  have hp := val4_eq_iff value.limbs params.modulus
  unfold NativeField.zakura_udon.field.pasta.PastaField.is_zero
  have hmodulus : inst.MODULUS=ok params.modulus := params.modulus_ok
  simp only [looseInst,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationReductionState,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed,
    NativeField.zakura_udon.field.pasta.representation.Loose.Insts.Zakura_udonFieldPastaRepresentationSealedSealed.REDUCED,
    hmodulus,index0_eq,index1_eq,index2_eq,index3_eq,bind_ok,Bool.false_eq_true,↓reduceIte]
  split_ifs <;> simp_all [WP.spec_ok,u64_eq_iff]

theorem decoded_zero_iff (p inverse a : Nat) (hinverse : Nat.ModEq p (R*inverse) 1) :
    (a*inverse)%p=0 ↔ a%p=0 := by
  constructor
  · intro h
    have hzero : Nat.ModEq p (a*inverse) 0 := by simpa only [Nat.ModEq,Nat.zero_mod] using h
    have hs := hzero.mul_left R
    have hi := hinverse.mul_left a
    have hcancel : Nat.ModEq p a 0 := by
      simpa only [mul_one] using hi.symm.trans (by convert hs using 1 <;> ring)
    simpa only [Nat.ModEq,Nat.zero_mod] using hcancel
  · intro h
    rw [Nat.mul_mod,h]
    simp

theorem loose_mod_zero_iff (p a : Nat) (hp : 0<p) (ha : a<2*p) :
    a%p=0 ↔ a=0 ∨ a=p := by
  have hdecomp := Nat.mod_add_div a p
  have hmod := Nat.mod_lt a hp
  have hquot : a/p<2 := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa only [mul_comm] using ha)
  constructor
  · intro h
    have hqnonneg : 0≤a/p := Nat.zero_le _
    have hcases : a/p=0 ∨ a/p=1 := by omega
    rcases hcases with hq | hq <;> simp only [h,hq,mul_zero,mul_one,zero_add] at hdecomp <;> omega
  · rintro (rfl | rfl) <;> simp

@[step]
theorem fp_is_zero_spec (value : Element Base Loose) (ha : val4 value.limbs < 2*fpPrime) :
    NativeField.fp_is_zero value ⦃ out => out=true ↔ decode fpPrime fpRadixInverse value.limbs=0 ⦄ := by
  unfold NativeField.fp_is_zero
  step -grind with (is_zero_loose_spec fpNativeInst fpNativeParameters value) as ⟨out,hout⟩
  rw [hout,decode,decoded_zero_iff fpPrime fpRadixInverse _ fp_radix_inverse]
  exact (loose_mod_zero_iff fpPrime _ fpParameters.positive ha).symm

@[step]
theorem fq_is_zero_spec (value : Element Scalar Loose) (ha : val4 value.limbs < 2*fqPrime) :
    NativeField.fq_is_zero value ⦃ out => out=true ↔ decode fqPrime fqRadixInverse value.limbs=0 ⦄ := by
  unfold NativeField.fq_is_zero
  step -grind with (is_zero_loose_spec fqNativeInst fqNativeParameters value) as ⟨out,hout⟩
  rw [hout,decode,decoded_zero_iff fqPrime fqRadixInverse _ fq_radix_inverse]
  exact (loose_mod_zero_iff fqPrime _ fqParameters.positive ha).symm

#print axioms fp_is_zero_spec
#print axioms fq_is_zero_spec
end UdonVerify.Native
