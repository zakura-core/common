import CommonProductAarch64ShortValue
import CommonProductAarch64SerialLoop
import CommonProductAarch64Setup
import CommonProductBlockDispatch

open Aeneas Std Result
namespace UdonVerify.ProductAarch64
open UdonVerify.Products UdonVerify.ProductBlock
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Every source dispatch arm on AArch64, for all supported slice lengths. -/
@[step]
theorem aarch64_slice_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < stateWeight s * val4 params.modulus)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < stateWeight t * val4 params.modulus) :
    CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice
      (aarch64Dict inst) left right lhs rhs ⦃ out =>
        val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs)
          (rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val) ⦄ := by
  by_cases hshort : lhs.length ≤ 3
  · exact slice_short_spec inst params left right s t hs ht lhs rhs hlen hshort ha hb
  · have hlenU : Aeneas.Std.Slice.len lhs = Aeneas.Std.Slice.len rhs :=
      UScalar.eq_of_val_eq (by simpa only [Aeneas.Std.Slice.len_val] using hlen)
    have hnotOne : Aeneas.Std.Slice.len lhs ≠ 1#usize := by scalar_tac
    have hnotShort : ¬ Aeneas.Std.Slice.len lhs ≤ 3#usize := by scalar_tac
    have hnotEmpty : lhs.length ≠ 0 := by omega
    have hbits : core.num.Usize.BITS ≤ 64#u32 := by
      change (core.num.Usize.BITS).val ≤ 64
      simpa [core.num.Usize.BITS] using System.Platform.numBits_le
    have hsumBound := bounded_sum_fits_accumulator (fun a => val4 a.limbs) (fun b => val4 b.limbs)
      lhs.val rhs.val hlen (slice_count_bound lhs) (fun a _ => val4_lt a.limbs) (fun b _ => val4_lt b.limbs)
    by_cases hblock : 32 ≤ lhs.length
    · have hblockU : Aeneas.Std.Slice.len lhs ≥ 32#usize := by scalar_tac
      unfold CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice
      simp only [←hlenU]
      simp [hbits,hnotOne,hnotShort,hnotEmpty,hblockU,core.slice.Slice.is_empty,massert,
        CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD]
      step -grind with (aarch64_new_spec M) as ⟨sum,hzero⟩
      step -grind with (chunks_thirty_two_spec lhs) as ⟨leftChunks,hpartL,hsizeL,hshapeL⟩
      step -grind with (chunks_thirty_two_spec rhs) as ⟨rightChunks,hpartR,hsizeR,hshapeR⟩
      have hshape : leftChunks.chunks.map (fun a => a.length) = rightChunks.chunks.map (fun b => b.length) := by
        rw [hshapeL,hshapeR,hlen]
      have hsplit := block_chunk_sum_flatten (fun a => val4 a.limbs) (fun b => val4 b.limbs)
        leftChunks.chunks rightChunks.chunks hshape
      rw [hpartL,hpartR] at hsplit
      simp only [core.iter.traits.iterator.Iterator.zip.trait_default,
        core.iter.traits.iterator.Iterator.zip.default,core.iter.traits.collect.IntoIterator.Blanket,
        core.iter.traits.collect.IntoIterator.Blanket.into_iter,Bind.bind,bind_ok]
      step -grind with (block_accumulation_spec (⟨leftChunks,rightChunks⟩ : BlockIter M S T) sum hshape hsizeL (by
        change sumInteger sum + chunkSum (fun a => val4 a.limbs) (fun b => val4 b.limbs)
          leftChunks.chunks rightChunks.chunks < B ^ 9
        omega)) as ⟨sum1,hsum1⟩
      change sumInteger sum1 = sumInteger sum + chunkSum (fun a => val4 a.limbs) (fun b => val4 b.limbs)
        leftChunks.chunks rightChunks.chunks at hsum1
      step -grind with (aarch64_finish_spec inst params constants sum1) as ⟨out,hout,hcert⟩
      refine ⟨hout,?_⟩
      have hexact : sumInteger sum1 = rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val := by omega
      simpa only [hexact] using hcert
    · have hblockU : ¬ Aeneas.Std.Slice.len lhs ≥ 32#usize := by scalar_tac
      have hserialU : Aeneas.Std.Slice.len lhs < 64#usize := by scalar_tac
      unfold CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice
      simp only [←hlenU]
      simp [hbits,hnotOne,hnotShort,hnotEmpty,hblockU,hserialU,core.slice.Slice.is_empty,massert,
        CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD]
      step -grind with (aarch64_new_spec M) as ⟨sum,hzero⟩
      simp only [core.slice.Slice.iter,core.iter.traits.iterator.Iterator.zip.trait_default,
        core.iter.traits.iterator.Iterator.zip.default,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,Bind.bind,bind_ok]
      step -grind with (aarch64_accumulation_spec inst params constants lhs rhs sum hlen (by omega)) as ⟨sum1,hsum⟩
      step -grind with (aarch64_finish_spec inst params constants sum1) as ⟨out,hout,hcert⟩
      exact ⟨hout,by simpa only [hsum,hzero,zero_add] using hcert⟩

@[step]
theorem aarch64_slice_value_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < stateWeight s * val4 params.modulus)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < stateWeight t * val4 params.modulus)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1) :
    CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice
      (aarch64Dict inst) left right lhs rhs ⦃ out =>
        val4 out.limbs < 2 * val4 params.modulus ∧
        Native.decode (val4 params.modulus) inverse out.limbs =
          decodedSum (val4 params.modulus) inverse lhs rhs ⦄ := by
  apply WP.spec_mono (aarch64_slice_spec inst params constants left right s t hs ht lhs rhs hlen ha hb)
  intro out hout
  refine ⟨hout.1,?_⟩
  have hscaled := Native.decoded_product_sum _ _ _ _ hinverse hout.2
  have hdecoded := raw_sum_decoded (fun a => val4 a.limbs) (fun b => val4 b.limbs)
    (val4 params.modulus) inverse lhs.val rhs.val
  exact hscaled.trans hdecoded.symm

#print axioms aarch64_slice_spec
#print axioms aarch64_slice_value_spec
end UdonVerify.ProductAarch64
