import NativeChunks
import NativeLongByteMath
import NativeWideConstructors

open Aeneas Std Result
open NativeField.zakura_udon.field.pasta.encoding.PastaField
namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem bytes_loop_unfold {M S : Type} (inst : Modulus M)
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (value : Element M Loose)
    (iter : core.iter.adapters.rev.Rev (_root_.core.slice.iter.Chunks U8)) :
    from_bytes_reduced_loop inst state value iter = (do
      let flow ← from_bytes_reduced_loop.body inst state value iter
      match flow with
      | .done out => ok out
      | .cont (v,it) => from_bytes_reduced_loop inst state v it) := by
  unfold from_bytes_reduced_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont pair => rcases pair with ⟨v,it⟩; rfl

/-- The actual reversed-chunk loop terminates and evaluates all remaining digits. -/
@[step]
theorem bytes_loop_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R*inverse) 1)
    (remaining : Aeneas.Std.Slice U8) (value : Element M Loose)
    (hmultiple : remaining.length % 32 = 0)
    (hbound : val4 value.limbs < 2*val4 params.modulus) :
    from_bytes_reduced_loop inst state value ⟨⟨remaining,32#usize⟩⟩
      ⦃ out => val4 out.limbs < 2*val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (val4 out.limbs)
          (R*byteValue remaining.val+256^remaining.length*val4 value.limbs) ⦄ := by
  generalize hn : remaining.length=n
  induction n using Nat.strong_induction_on generalizing remaining value with
  | h n ih =>
    rw [bytes_loop_unfold]
    unfold from_bytes_reduced_loop.body
    simp only [core.marker.PhantomData.Insts.CoreCloneClone.clone, bind_ok,
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
      NativeField.core.slice.iter.Chunks.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedSlice,
      Std.bind_assoc]
    have hback := chunks_back_multiple_eq remaining hmultiple
    unfold chunksBack at hback
    rw [hback]
    by_cases hzero : remaining.length=0
    · simp only [hzero,↓reduceIte]
      simp only [bind_tc_eq,bind_ok,Std.uncurry,WP.spec_ok]
      have hempty : remaining.val=[] := List.eq_nil_of_length_eq_zero hzero
      refine ⟨hbound,?_⟩
      simp [Nat.ModEq,hempty,←hn,byteValue]
    · simp only [hzero,↓reduceIte,bind_ok]
      obtain ⟨hsize,hsuffix,hprefix,hmultNext,hlt⟩ :=
        full_chunk_facts remaining hmultiple (by omega)
      step -grind as ⟨chunkResult,hchunkResult⟩
      cases chunkResult with
      | Err error => cases error; simp only at hchunkResult; omega
      | Ok chunkBytes =>
        simp only at hchunkResult
        simp only [core.result.Result.unwrap,bind_ok]
        step -grind with (uint_from_bytes_spec chunkBytes) as ⟨digit,hdigit⟩
        rw [constants.conversion.radix2_ok]
        simp only [NativeField.zakura_udon.field.pasta.uint.CanonicalUint.impl.limbs,bind_ok]
        have hsumBound := horner_raw_products_bound inst params constants
          (val4 value.limbs) (val4 digit.limbs) hbound (val4_lt _)
        step -grind with (raw_product_sum_spec inst params value.limbs constants.conversion.radix2
          digit.limbs constants.conversion.radix2 hsumBound) as ⟨limbs,hlimbs,m,hm,hcert⟩
        step -grind with (from_montgomery_loose_spec inst params limbs hlimbs) as ⟨current,hcurrent⟩
        have hdigitVal : val4 digit.limbs=byteValue (byteSuffix remaining (remaining.length-32)).val := by
          rw [hdigit,hchunkResult.1]
        have hr2 : Nat.ModEq (val4 params.modulus) (val4 constants.conversion.radix2) (R^2) := by
          simp only [Nat.ModEq,constants.conversion.radix2_val,Nat.mod_mod]
        have hproduct : Nat.ModEq (val4 params.modulus)
            (val4 value.limbs*val4 constants.conversion.radix2+
              val4 digit.limbs*val4 constants.conversion.radix2)
            (R*(R*(val4 value.limbs+val4 digit.limbs))) := by
          convert hr2.mul_left (val4 value.limbs+val4 digit.limbs) using 1 <;> ring
        have hrawNext : Nat.ModEq (val4 params.modulus) (val4 current.limbs)
            (R*(val4 value.limbs+val4 digit.limbs)) := by
          rw [hcurrent]
          exact raw_result_congruence _ inverse _ _ m _ hinverse hproduct hcert
        have hboundNext : val4 current.limbs<2*val4 params.modulus := by
          simpa only [hcurrent] using hlimbs
        step -grind with (ih (bytePrefix remaining (remaining.length-32)).length (by omega)
          (bytePrefix remaining (remaining.length-32)) current hmultNext hboundNext rfl)
          as ⟨out,hout,hvalue⟩
        refine ⟨hout,?_⟩
        have hcompose := (hrawNext.mul_left (256^(bytePrefix remaining (remaining.length-32)).length)).add_left
          (R*byteValue (bytePrefix remaining (remaining.length-32)).val)
        have hbytes := byteValue_prefix_suffix remaining (remaining.length-32) (by omega)
        have hpow : 256^remaining.length=256^(remaining.length-32)*R := by
          conv_lhs => rw [show remaining.length=(remaining.length-32)+32 by omega]
          rw [pow_add]
          norm_num [R,B]
        apply hvalue.trans
        rw [hprefix,hdigitVal] at hcompose
        rw [←hn,hbytes,hpow,hprefix]
        convert hcompose using 1 <;> ring

#print axioms bytes_loop_unfold
#print axioms bytes_loop_spec
end UdonVerify.Native
