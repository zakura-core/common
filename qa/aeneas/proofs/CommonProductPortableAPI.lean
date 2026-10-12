import CommonProductPortableShortValue
import CommonProductPortableSerialLoop
import CommonProductPortableChunkLoop
import CommonProductPortableRemainderLoop
import CommonProductPortableMergeLoop
import CommonProductPortableSetup

open Aeneas Std Result
namespace UdonVerify.ProductPortable
open UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Complete portable slice dispatch, with no term limit beyond the slice model. -/
@[step]
theorem portable_slice_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < stateWeight s * val4 params.modulus)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < stateWeight t * val4 params.modulus) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice
      (portableDict inst) left right lhs rhs ⦃ out =>
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
    unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice
    simp only [←hlenU]
    simp [hbits,hnotOne,hnotShort,hnotEmpty,core.slice.Slice.is_empty,massert,
      CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.LANE_THRESHOLD,
      CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.LANES]
    by_cases hserial : lhs.length < 64
    · rw [if_pos hserial]
      step -grind with (portable_new_spec M) as ⟨sum,hzero⟩
      simp only [core.slice.Slice.iter,core.iter.traits.iterator.Iterator.zip.trait_default,
        core.iter.traits.iterator.Iterator.zip.default,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,Bind.bind,bind_ok]
      step -grind with (portable_accumulation_spec inst params constants lhs rhs sum hlen (by omega)) as ⟨sum1,hsum⟩
      step -grind with (portable_finish_spec inst params constants sum1) as ⟨out,hout,hcert⟩
      exact ⟨hout,by simpa only [hsum,hzero,zero_add] using hcert⟩
    · rw [if_neg hserial]
      step -grind with (initial_lanes_spec M S T) as ⟨lanes,hzero⟩
      step -grind with (chunks_exact_four_spec lhs) as ⟨leftChunks,hpartL,hfullL,hremL,hcountL,hmodL⟩
      step -grind with (chunks_exact_four_spec rhs) as ⟨rightChunks,hpartR,hfullR,hremR,hcountR,hmodR⟩
      have hchunksLen : leftChunks.chunks.length = rightChunks.chunks.length := by rw [hcountL,hcountR,hlen]
      have hremainderLen : leftChunks.remainder.length = rightChunks.remainder.length := by rw [hmodL,hmodR,hlen]
      have hsplit := chunk_sum_flatten (fun a => val4 a.limbs) (fun b => val4 b.limbs)
        leftChunks.chunks rightChunks.chunks leftChunks.remainder.val rightChunks.remainder.val
        hchunksLen hfullL hfullR
      rw [hpartL,hpartR] at hsplit
      simp only [core.iter.traits.iterator.Iterator.zip.trait_default,core.iter.traits.iterator.Iterator.zip.default,
        core.iter.traits.collect.IntoIterator.Blanket,core.iter.traits.collect.IntoIterator.Blanket.into_iter,
        Bind.bind,bind_ok]
      step -grind with (chunk_accumulation_spec inst params constants
        (⟨leftChunks,rightChunks⟩ : ChunkIter M S T) lanes hchunksLen hfullL hfullR (by
          change lanesInteger lanes + chunkSum (fun x => val4 x.limbs) (fun y => val4 y.limbs)
            leftChunks.chunks rightChunks.chunks < B ^ 9
          omega)) as ⟨lanes1,hvalue1⟩
      change lanesInteger lanes1 = lanesInteger lanes +
        chunkSum (fun x => val4 x.limbs) (fun y => val4 y.limbs) leftChunks.chunks rightChunks.chunks at hvalue1
      simp only [core.slice.iter.ChunksExact.getRemainder,core.slice.Slice.iter,
        core.iter.traits.iterator.Iterator.zip.trait_default,core.iter.traits.iterator.Iterator.zip.default,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,Bind.bind,bind_ok]
      step -grind with (remainder_accumulation_spec inst params constants
        leftChunks.remainder rightChunks.remainder lanes1 hremainderLen (by omega)) as ⟨lanes2,hvalue2⟩
      step -grind with (portable_new_spec M) as ⟨sum,hzeroSum⟩
      simp only [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
      let laneSlice : Aeneas.Std.Slice (Sum M) := Aeneas.Std.Slice.from lanes2.val (by scalar_tac)
      have hlanesList : (laneSlice.val.map sumInteger).sum = lanesInteger lanes2 := by
        simpa only [laneSlice,Aeneas.Std.Slice.from_val] using lane_list_sum lanes2
      step -grind with (merge_accumulation_spec (portableDict inst) laneSlice sum (by omega))
        as ⟨sum1,hmerged⟩
      have hmergedValue : sumInteger sum1 = sumInteger sum + lanesInteger lanes2 := by
        simpa only [laneSlice,Aeneas.Std.Slice.from_val,lane_list_sum] using hmerged
      step -grind with (portable_finish_spec inst params constants sum1) as ⟨out,hout,hcert⟩
      refine ⟨hout,?_⟩
      have hexact : sumInteger sum1 = rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val := by omega
      simpa only [hexact] using hcert

@[step]
theorem portable_slice_value_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < stateWeight s * val4 params.modulus)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < stateWeight t * val4 params.modulus)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice
      (portableDict inst) left right lhs rhs ⦃ out =>
        val4 out.limbs < 2 * val4 params.modulus ∧
        Native.decode (val4 params.modulus) inverse out.limbs =
          decodedSum (val4 params.modulus) inverse lhs rhs ⦄ := by
  apply WP.spec_mono (portable_slice_spec inst params constants left right s t hs ht lhs rhs hlen ha hb)
  intro out hout
  refine ⟨hout.1,?_⟩
  have hscaled := Native.decoded_product_sum _ _ _ _ hinverse hout.2
  have hdecoded := raw_sum_decoded (fun a => val4 a.limbs) (fun b => val4 b.limbs)
    (val4 params.modulus) inverse lhs.val rhs.val
  exact hscaled.trans hdecoded.symm

#print axioms portable_slice_spec
#print axioms portable_slice_value_spec
end UdonVerify.ProductPortable
