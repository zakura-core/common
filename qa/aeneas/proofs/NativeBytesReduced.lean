import NativeBytesLoop

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The public decoder reduces every finite byte slice, including the empty slice. -/
@[step]
theorem from_bytes_reduced_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (state : NativeField.zakura_udon.field.pasta.representation.ReductionState S)
    (bound inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (bytes : Aeneas.Std.Slice U8)
    (hconstructor : ∀ limbs : A4, val4 limbs < 2 * val4 params.modulus →
      NativeField.zakura_udon.field.pasta.PastaField.from_loose inst state limbs
        ⦃ out => val4 out.limbs < bound ∧
          Nat.ModEq (val4 params.modulus) (val4 out.limbs) (val4 limbs) ⦄) :
    NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes_reduced inst state bytes
      ⦃ out => val4 out.limbs < bound ∧
        decode (val4 params.modulus) inverse out.limbs =
          byteValue bytes.val % val4 params.modulus ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.encoding.PastaField.from_bytes_reduced
  simp only [NativeField.zakura_udon.field.pasta.ENCODED_SIZE]
  split
  · have hfit : bytes.length ≤ 32 := by scalar_tac
    step +scalarTac -grind as ⟨prefixSlice, back, hprefix, hprefixLen, hback⟩
    step +scalarTac -grind as ⟨copied, hcopied⟩
    have hpadded : byteValue (back copied).val = byteValue bytes.val := by
      rw [hback, hcopied]
      simpa [Array.repeat_val] using byteValue_padded_prefix bytes.val 32 hfit
    step -grind with (uint_from_bytes_spec (back copied)) as ⟨uint, huint⟩
    step -grind with (from_uint_reduced_spec inst params constants.conversion state bound inverse
      hinverse uint hconstructor) as ⟨out, hout, hdecode⟩
    exact ⟨hout, by simpa only [huint, hpadded] using hdecode⟩
  · step +scalarTac -grind with Usize.mul_spec as ⟨width, hwidth⟩
    have hwidthEq : width = 64#usize := by scalar_tac
    subst width
    split
    · have hfit : bytes.length ≤ 64 := by scalar_tac
      step +scalarTac -grind as ⟨prefixSlice, back, hprefix, hprefixLen, hback⟩
      step +scalarTac -grind as ⟨copied, hcopied⟩
      have hpadded : byteValue (back copied).val = byteValue bytes.val := by
        rw [hback, hcopied]
        simpa [Array.repeat_val] using byteValue_padded_prefix bytes.val 64 hfit
      step -grind with (from_wide_bytes_reduced_spec inst params constants state bound inverse
        hinverse (back copied) hconstructor) as ⟨out, hout, hdecode⟩
      exact ⟨hout, by simpa only [hpadded] using hdecode⟩
    · have hpositive : 0 < bytes.length := by scalar_tac
      obtain ⟨hsplit,hhighPositive,hhighFit,hprefixLength,hmultiple⟩ :=
        initial_chunk_facts bytes hpositive
      simp only [_root_.core.slice.Slice.chunks,
        show (32#usize).val ≠ 0 from by decide,massert_True,bind_ok,
        core.iter.traits.iterator.Iterator.rev.trait_default,
        core.iter.traits.iterator.Iterator.rev.default,
        core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,Std.bind_assoc]
      have hnext := chunks_back_initial_eq bytes hpositive
      unfold chunksBack at hnext
      rw [hnext]
      simp only [core.option.Option.unwrap,bind_tc_eq,Std.uncurry,bind_ok]
      simp only [show (32#usize).val ≠ 0 from by decide,massert_True,
        bind_ok,ofOption]
      step +scalarTac -grind
      step +scalarTac -grind as ⟨prefixSlice,back,hprefix,hprefixLen,hback⟩
      step +scalarTac -grind as ⟨copied,hcopied⟩
      have hpadded : byteValue (back copied).val = byteValue (byteSuffix bytes (initialSplit bytes)).val := by
        rw [hback,hcopied]
        simpa [Array.repeat_val] using byteValue_padded_prefix
          (byteSuffix bytes (initialSplit bytes)).val 32 hhighFit
      step -grind with (uint_from_bytes_spec (back copied)) as ⟨uint,huint⟩
      step -grind with (from_uint_reduced_spec inst params constants.conversion looseInst
        (2*val4 params.modulus) inverse hinverse uint
        (loose_constructor_value_spec inst params)) as ⟨value,hbound,hdecode⟩
      have hraw : Nat.ModEq (val4 params.modulus) (val4 value.limbs)
          (R*byteValue (byteSuffix bytes (initialSplit bytes)).val) := by
        unfold decode at hdecode
        rw [huint,hpadded] at hdecode
        exact montgomery_of_decode _ inverse _ _ hinverse hdecode
      step -grind with (bytes_loop_spec inst params constants state inverse hinverse
        (bytePrefix bytes (initialSplit bytes)) value hmultiple hbound) as ⟨current,hcurrent,hloop⟩
      have hwhole : Nat.ModEq (val4 params.modulus) (val4 current.limbs)
          (R*byteValue bytes.val) := by
        have hscaled := (hraw.mul_left (256^(initialSplit bytes))).add_left
          (R*byteValue (bytePrefix bytes (initialSplit bytes)).val)
        have hbytes := byteValue_prefix_suffix bytes (initialSplit bytes) hsplit
        apply hloop.trans
        rw [hprefixLength,hbytes]
        convert hscaled using 1 <;> ring
      step -grind with (hconstructor current.limbs hcurrent) as ⟨out,hout,hcongruence⟩
      exact ⟨hout,decode_of_montgomery _ inverse _ _ hinverse (hcongruence.trans hwhole)⟩

#print axioms from_bytes_reduced_spec

end UdonVerify.Native
