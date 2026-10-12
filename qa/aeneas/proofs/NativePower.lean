import NativePowerHelpers

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev arithmeticInst {M : Type} (inst : Modulus M) :=
  NativeField.zakura_udon.field.pasta.PastaFieldMLoose.Insts.Zakura_udonFieldPastaAlgorithmsField inst

@[step]
theorem arithmetic_square_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (value : Element M Loose) (ha : val4 value.limbs<2*val4 params.modulus) :
    (arithmeticInst inst).square value ⦃ out =>
      val4 out.limbs<2*val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs=
        (decode (val4 params.modulus) inverse value.limbs)^2%val4 params.modulus ⦄ := by
  change NativeField.zakura_udon.field.pasta.PastaField.square inst value ⦃ out => _ ⦄
  step -grind with (square_spec inst params value ha) as ⟨out,hbound,m,hm,hcert⟩
  refine ⟨hbound,?_⟩
  simpa only [pow_two,decode] using decoded_product (val4 params.modulus) inverse
    (val4 value.limbs) (val4 value.limbs) (val4 out.limbs) m hinverse
    (by simpa only [pow_two] using hcert)

@[step]
theorem arithmetic_multiply_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (lhs rhs : Element M Loose) (ha : val4 lhs.limbs<2*val4 params.modulus)
    (hb : val4 rhs.limbs<2*val4 params.modulus) :
    (arithmeticInst inst).mul lhs rhs ⦃ out =>
      val4 out.limbs<2*val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs=
        (decode (val4 params.modulus) inverse lhs.limbs*
          decode (val4 params.modulus) inverse rhs.limbs)%val4 params.modulus ⦄ := by
  change NativeField.zakura_udon.field.pasta.PastaField.mul inst lhs rhs ⦃ out => _ ⦄
  step -grind with (multiply_spec inst params lhs rhs ha hb) as ⟨out,hbound,m,hm,hcert⟩
  exact ⟨hbound,decoded_product (val4 params.modulus) inverse _ _ _ m hinverse hcert⟩

@[step]
theorem arithmetic_one_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1) :
    (arithmeticInst inst).ONE ⦃ out => val4 out.limbs<2*val4 params.modulus ∧
      decode (val4 params.modulus) inverse out.limbs=1 ⦄ := by
  change NativeField.zakura_udon.field.pasta.PastaFieldMLoose.Insts.Zakura_udonFieldPastaAlgorithmsField.ONE inst
    ⦃ out => _ ⦄
  unfold NativeField.zakura_udon.field.pasta.PastaFieldMLoose.Insts.Zakura_udonFieldPastaAlgorithmsField.ONE
  have hp : 1<val4 params.modulus := by
    have h := params.offset_positive
    norm_num only [R,B] at h
    omega
  step -grind with (one_spec inst params constants inverse hinverse hp Loose) as ⟨out,hbound,hvalue⟩
  exact ⟨by omega,hvalue⟩

theorem power_loop_unfold {F : Type}
    (inst : NativeField.zakura_udon.field.pasta.algorithms.Field F) (iter : Reverse32)
    (value : F) (exponent : U64) (result : F) :
    NativeField.zakura_udon.field.pasta.algorithms.pow_u64_loop inst iter value exponent result =
      (do
        let flow ← NativeField.zakura_udon.field.pasta.algorithms.pow_u64_loop.body inst value exponent iter result
        match flow with
        | .done out => ok out
        | .cont (next,current) =>
          NativeField.zakura_udon.field.pasta.algorithms.pow_u64_loop inst next value exponent current) := by
  unfold NativeField.zakura_udon.field.pasta.algorithms.pow_u64_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont pair => rcases pair with ⟨next,current⟩; rfl

@[step]
theorem power_loop_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (inverse : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (value : Element M Loose) (exponent : U64)
    (ha : val4 value.limbs<2*val4 params.modulus) (iter : Reverse32) (result : Element M Loose)
    (hstart : iter.iter.start=0#u32) (hend : iter.iter.end.val≤63)
    (hr : val4 result.limbs<2*val4 params.modulus)
    (hprefix : decode (val4 params.modulus) inverse result.limbs=
      (decode (val4 params.modulus) inverse value.limbs)^(exponent.val/2^iter.iter.end.val)%val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.algorithms.pow_u64_loop (arithmeticInst inst) iter value exponent result
      ⦃ out => val4 out.limbs<2*val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs=
          (decode (val4 params.modulus) inverse value.limbs)^exponent.val%val4 params.modulus ⦄ := by
  generalize hn : iter.iter.end.val=n
  induction n using Nat.strong_induction_on generalizing iter result with
  | h n ih =>
    rw [power_loop_unfold]
    unfold NativeField.zakura_udon.field.pasta.algorithms.pow_u64_loop.body
    by_cases hpos : 0 < iter.iter.end.val
    · have hnext := WP.spec_imp_exists (reverse32_some_spec iter hstart hpos)
      rcases hnext with ⟨⟨opt,next⟩,hnext,bit,hopt,hstart',hend',hbit⟩
      subst opt
      unfold reverse32Next at hnext
      rw [hnext]
      simp only [bind_ok,Std.uncurry_apply_pair,Std.bind_assoc]
      step -grind with (arithmetic_square_spec inst params inverse hinverse result hr)
        as ⟨squared,hsbound,hsquare⟩
      step -grind with (U64.ShiftLeft_spec 1#u64 bit (by omega)) as ⟨mask,hmask,hmaskb⟩
      have hpowBound : 2^bit.val<U64.size := by
        simp only [U64.size,U64.numBits,UScalarTy.numBits]
        exact Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
      have hmaskval : mask.val=2^bit.val := by
        simpa only [Nat.shiftLeft_eq,one_mul,Nat.mod_eq_of_lt hpowBound] using hmask
      step -grind with UScalar.and_spec as ⟨bits,hbits,hbitsb⟩
      have hflag : bits.val=if exponent.val/2^bit.val%2=1 then 2^bit.val else 0 := by
        simp only [UScalar.val_and,hmaskval] at hbits
        exact hbits.trans (and_power_bit exponent.val bit.val)
      have hsplit := prefix_step exponent.val bit.val
      rw [hbit] at hsplit
      have hsquared : decode (val4 params.modulus) inverse squared.limbs=
          (decode (val4 params.modulus) inverse value.limbs)^(2*(exponent.val/2^iter.iter.end.val))%val4 params.modulus := by
        rw [hsquare,hprefix]
        simp only [←Nat.pow_mod,Nat.mod_mod]
        rw [←pow_mul]
        congr 2
        ring
      split
      · rename_i hnonzero
        have hrem : exponent.val/2^bit.val%2=1 := by
          by_contra h
          rw [if_neg h] at hflag
          have hbitszero : bits=0#u64 := UScalar.eq_of_val_eq hflag
          simp [hbitszero] at hnonzero
        step -grind with (arithmetic_multiply_spec inst params inverse hinverse squared value hsbound ha)
          as ⟨current,hcurrent,hmul⟩
        have hinvariant : decode (val4 params.modulus) inverse current.limbs=
            (decode (val4 params.modulus) inverse value.limbs)^(exponent.val/2^next.iter.end.val)%val4 params.modulus := by
          rw [hend',hmul,hsquared]
          have hexponent : exponent.val/2^bit.val=2*(exponent.val/2^iter.iter.end.val)+1 := by omega
          rw [hexponent,pow_succ]
          simp only [Nat.mul_mod,Nat.mod_mod]
        have hmeasure : bit.val<n := by omega
        step -grind with (ih bit.val hmeasure next current hstart' (by rw [hend']; omega)
          hcurrent hinvariant (by rw [hend'])) as ⟨out,hout,hvalue⟩
        exact ⟨hout,hvalue⟩
      · rename_i hzero
        have hbitszero : bits.val=0 := by simpa using hzero
        have hrem : exponent.val/2^bit.val%2=0 := by
          have hlt := Nat.mod_lt (exponent.val/2^bit.val) (by decide : 0<2)
          by_contra h
          have hone : exponent.val/2^bit.val%2=1 := by omega
          rw [if_pos hone] at hflag
          have hp : 0<2^bit.val := pow_pos (by decide) _
          have hbad : 0=2^bit.val := hbitszero.symm.trans hflag
          omega
        have hinvariant : decode (val4 params.modulus) inverse squared.limbs=
            (decode (val4 params.modulus) inverse value.limbs)^(exponent.val/2^next.iter.end.val)%val4 params.modulus := by
          rw [hend',hsquared]
          congr 2
          omega
        have hmeasure : bit.val<n := by omega
        step -grind with (ih bit.val hmeasure next squared hstart' (by rw [hend']; omega)
          hsbound hinvariant (by rw [hend'])) as ⟨out,hout,hvalue⟩
        exact ⟨hout,hvalue⟩
    · have hz : iter.iter.end.val=0 := by omega
      have hnext := WP.spec_imp_exists (reverse32_none_spec iter hstart hz)
      rcases hnext with ⟨⟨opt,next⟩,hnext,hopt,hiter⟩
      subst opt
      subst next
      unfold reverse32Next at hnext
      rw [hnext]
      simp only [bind_ok,Std.uncurry_apply_pair,WP.spec_ok]
      exact ⟨hr,by simpa only [hz,pow_zero,Nat.div_one] using hprefix⟩

@[step]
theorem pow_u64_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : ConversionParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (value : Element M S) (exponent : U64) (ha : val4 value.limbs<2*val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.PastaField.pow_u64 inst value exponent ⦃ out =>
      val4 out.limbs<2*val4 params.modulus ∧ decode (val4 params.modulus) inverse out.limbs=
        (decode (val4 params.modulus) inverse value.limbs)^exponent.val%val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.PastaField.pow_u64
  step -grind with (widen_spec value) as ⟨loose,hloose⟩
  unfold NativeField.zakura_udon.field.pasta.algorithms.pow_u64
  split
  · have he : exponent.val=0 := by scalar_tac
    step -grind with (arithmetic_one_spec inst params constants inverse hinverse) as ⟨out,hbound,hvalue⟩
    have hp : 1<val4 params.modulus := by
      have h := params.offset_positive
      norm_num only [R,B] at h
      omega
    exact ⟨hbound,by simp only [hvalue,he,pow_zero,Nat.mod_eq_of_lt hp]⟩
  · have hne : exponent.val≠0 := by scalar_tac
    have hleading := leading_zeros_nonzero exponent hne
    have hhighest := highest_bit_spec exponent hne
    simp only [lift,bind_ok]
    step -grind with UScalar.sub_spec as ⟨highest,hvalue⟩
    have hhighestval : highest.val=Nat.log 2 exponent.val := by scalar_tac
    step -grind with core.iter.traits.iterator.Iterator.rev.trait_default.spec as ⟨iter,hiter⟩
    have hstart : iter.iter.start=0#u32 := by rw [hiter]
    have hend : iter.iter.end.val≤63 := by rw [hiter]; change highest.val≤63; omega
    have hprefix : decode (val4 params.modulus) inverse loose.limbs=
        (decode (val4 params.modulus) inverse loose.limbs)^(exponent.val/2^iter.iter.end.val)%val4 params.modulus := by
      rw [hiter]
      change _ = _^(exponent.val/2^highest.val)%val4 params.modulus
      rw [hhighestval,hhighest.2]
      simp only [pow_one,decode,Nat.mod_mod]
    step -grind with (power_loop_spec inst params inverse hinverse loose exponent
      (by simpa only [hloose] using ha) iter loose hstart hend
      (by simpa only [hloose] using ha) hprefix) as ⟨out,hbound,hvalue⟩
    exact ⟨hbound,by simpa only [decode,hloose] using hvalue⟩

@[step]
theorem fp_pow_u64_spec (value : Element Base Loose) (exponent : U64)
    (ha : val4 value.limbs<2*fpPrime) : NativeField.fp_pow_u64 value exponent
    ⦃ out => val4 out.limbs<2*fpPrime ∧ decode fpPrime fpRadixInverse out.limbs=
      (decode fpPrime fpRadixInverse value.limbs)^exponent.val%fpPrime ⦄ := by
  unfold NativeField.fp_pow_u64
  step -grind with (pow_u64_spec fpNativeInst fpNativeParameters fpConversionParameters
    fpRadixInverse fp_radix_inverse value exponent ha) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

#print axioms fp_pow_u64_spec


@[step]
theorem fq_pow_u64_spec (value : Element Scalar Loose) (exponent : U64)
    (ha : val4 value.limbs<2*fqPrime) : NativeField.fq_pow_u64 value exponent
    ⦃ out => val4 out.limbs<2*fqPrime ∧ decode fqPrime fqRadixInverse out.limbs=
      (decode fqPrime fqRadixInverse value.limbs)^exponent.val%fqPrime ⦄ := by
  unfold NativeField.fq_pow_u64
  step -grind with (pow_u64_spec fqNativeInst fqNativeParameters fqConversionParameters
    fqRadixInverse fq_radix_inverse value exponent ha) as ⟨out,hbound,hvalue⟩
  exact ⟨hbound,hvalue⟩

#print axioms fq_pow_u64_spec

#print axioms pow_u64_spec
end UdonVerify.Native
