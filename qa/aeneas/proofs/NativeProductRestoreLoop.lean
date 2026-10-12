import NativeProductWords
import NativeBits
import NativeSmallLoop
import NativeProductHigh

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
attribute [local reducible] WP.Post

def maskWords (offset : A4) (mask : U64) : A4 :=
  Array.make 4#usize [offset[0]! &&& mask, offset[1]! &&& mask,
    offset[2]! &&& mask, offset[3]! &&& mask]

theorem mask_words_zero (offset : A4) : val4 (maskWords offset 0#u64) = 0 := by
  simp [maskWords, and_zero, val4]

theorem mask_words_full (offset : A4) : val4 (maskWords offset fullMask) = val4 offset := by
  simp [maskWords, and_full, val4]

open NativeField.zakura_udon.field.pasta.products.PastaField
abbrev RestoreZip := core.iter.adapters.zip.Zip (core.slice.iter.IterMut U64)
  (core.array.iter.IntoIter U64 4#usize)
theorem product_restore_loop_unfold (iter : RestoreZip) (back : RestoreZip → RestoreZip)
    (mask carry : U64) : product_difference_loop2 iter back mask carry = (do
      let r ← product_difference_loop2.body mask iter back carry
      match r with
      | .done out => ok out
      | .cont (it,b,c) => product_difference_loop2 it b mask c) := by
  unfold product_difference_loop2
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨it,b,c⟩; rfl

@[step]
theorem product_restore_loop_spec_four (mask a0 a1 a2 a3 b0 b1 b2 b3 : U64) :
    product_difference_loop2 ⟨⟨Slice.from [a0,a1,a2,a3] (by scalar_tac),0⟩,
       ⟨Slice.from [b0,b1,b2,b3] (by scalar_tac),0⟩⟩ (fun z => z) mask 0#u64
      ⦃ carry z back => (back z).fst.slice.length=4 ∧ carry.val≤1 ∧
        val4 (Array.from_slice (Array.make 4#usize [a0,a1,a2,a3]) (back z).fst.slice)
          + R*carry.val = val4 (Array.make 4#usize [a0,a1,a2,a3]) +
            val4 (Array.make 4#usize [b0 &&& mask,b1 &&& mask,b2 &&& mask,b3 &&& mask]) ⦄ := by
  rw [product_restore_loop_unfold]
  unfold product_difference_loop2.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  step -grind with UScalar.and_spec as ⟨m0,hm0,hmb0⟩
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair0,h0⟩
  rcases pair0 with ⟨r0,c0⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [product_restore_loop_unfold]
  unfold product_difference_loop2.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  step -grind with UScalar.and_spec as ⟨m1,hm1,hmb1⟩
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair1,h1⟩
  rcases pair1 with ⟨r1,c1⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [product_restore_loop_unfold]
  unfold product_difference_loop2.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  step -grind with UScalar.and_spec as ⟨m2,hm2,hmb2⟩
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair2,h2⟩
  rcases pair2 with ⟨r2,c2⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [product_restore_loop_unfold]
  unfold product_difference_loop2.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  step -grind with UScalar.and_spec as ⟨m3,hm3,hmb3⟩
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair3,h3⟩
  rcases pair3 with ⟨r3,c3⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [product_restore_loop_unfold]
  unfold product_difference_loop2.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    WP.spec_ok]
  change r0.val+B*c0.val=a0.val+m0.val+0 at h0
  change m0.val=(b0 &&& mask).val at hm0
  change r1.val+B*c1.val=a1.val+m1.val+c0.val at h1
  change m1.val=(b1 &&& mask).val at hm1
  change r2.val+B*c2.val=a2.val+m2.val+c1.val at h2
  change m2.val=(b2 &&& mask).val at hm2
  change r3.val+B*c3.val=a3.val+m3.val+c2.val at h3
  change m3.val=(b3 &&& mask).val at hm3
  have hc0 : c0.val≤1 := by
    have h := h0
    norm_num only [B] at h
    scalar_tac
  have hc1 : c1.val≤1 := by
    have h := h1
    norm_num only [B] at h
    scalar_tac
  have hc2 : c2.val≤1 := by
    have h := h2
    norm_num only [B] at h
    scalar_tac
  have hc3 : c3.val≤1 := by
    have h := h3
    norm_num only [B] at h
    scalar_tac
  refine ⟨hc3,?_⟩
  rw [small_restore_four]
  simp [val4]
  simp only [UScalar.val_and] at hm0 hm1 hm2 hm3
  rw [←hm0,←hm1,←hm2,←hm3]
  unfold R
  linear_combination h0+B*h1+B^2*h2+B^3*h3

@[step]
theorem product_restore_loop_upper_spec (mask : U64) (a b : A4) :
    product_difference_loop2 ⟨⟨a.to_slice,0⟩,⟨b.to_slice,0⟩⟩ (fun z => z) mask 0#u64
      ⦃ carry z back => (back z).fst.slice.length=4 ∧ carry.val≤1 ∧
        val4 (Array.from_slice a (back z).fst.slice)+R*carry.val=val4 a+
          val4 (Array.make 4#usize [b[0]! &&& mask,b[1]! &&& mask,b[2]! &&& mask,b[3]! &&& mask]) ⦄ := by
  obtain ⟨a0,a1,a2,a3,ha⟩ : ∃ a0 a1 a2 a3 : U64,
      a=Array.make 4#usize [a0,a1,a2,a3] :=
    ⟨a[0]!,a[1]!,a[2]!,a[3]!,CommonVerify.array_four_eta a⟩
  obtain ⟨b0,b1,b2,b3,hb⟩ : ∃ b0 b1 b2 b3 : U64,
      b=Array.make 4#usize [b0,b1,b2,b3] :=
    ⟨b[0]!,b[1]!,b[2]!,b[3]!,CommonVerify.array_four_eta b⟩
  subst a b
  simpa [Array.to_slice] using product_restore_loop_spec_four mask a0 a1 a2 a3 b0 b1 b2 b3


/-- The actual upper-slice borrow and restoration sequence. -/
def productRestoreWords (wide : A8) (mask : U64) (offset : A4) : Result (A8 × U64) := do
  let (s,index_back) ← core.array.Array.index_mut
    (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U64))
    wide {start:=4#usize}
  let (im,iter_back) ← core.slice.Slice.iter_mut s
  let (it,zip_back) ← mutableZipCtor
    (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
    (NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter U64 4#usize) im offset
  let (carry,z,back) ← product_difference_loop2 it (fun z=>z) mask 0#u64
  ok (index_back (iter_back (zip_back (back z))),carry)

@[step]
theorem product_restore_loop_spec (wide : A8) (mask : U64) (offset : A4) :
    productRestoreWords wide mask offset ⦃ out carry => carry.val≤1 ∧
      val8 out+R^2*carry.val=val8 wide+R*val4 (maskWords offset mask) ⦄ := by
  unfold productRestoreWords
  step -grind with (Array.index_mut_SliceIndexRangeFromUsizeSlice wide
    {start:=4#usize} (by decide)) as ⟨s,index_back,hs,hlen,hback⟩
  have hs' : s=(productHigh wide).to_slice := by
    apply Slice.ext
    rw [hs]
    rw [array_eight_eta wide]
    simp [productHigh, Array.to_slice]
  subst s
  simp only [core.slice.Slice.iter_mut, mutableZipCtor,
    NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter,
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    bind_ok,Std.uncurry_apply_pair]
  obtain ⟨triple,hresult,hspec⟩ := WP.spec_imp_exists
    (product_restore_loop_upper_spec mask (productHigh wide) offset)
  rcases triple with ⟨carry,z,back⟩
  rcases hspec with ⟨hrestoredLength,hcarry,hvalue⟩
  simp only [Array.to_slice] at hresult ⊢
  rw [hresult]
  simp only [bind_ok,WP.spec_ok]
  let tail : A4 := Array.from_slice (productHigh wide) (back z).fst.slice
  have htail : tail.val=(back z).fst.slice.val := by
    exact Array.from_slice_val _ _ (by simpa using hrestoredLength)
  have hvalues : (index_back (back z).fst.slice).val=wide.val.setSlice! 4 tail.val := by
    rw [hback (back z).fst.slice,htail]
  have hout := upper_splice_value wide tail (index_back (back z).fst.slice) hvalues
  try simp only [WP.spec_ok]
  refine ⟨hcarry,?_⟩
  change val4 tail+R*carry.val=val4 (productHigh wide)+val4 (maskWords offset mask) at hvalue
  rw [hout, product_halves_value]
  simp [productLow,val4] at hvalue ⊢
  simp only [R] at hvalue ⊢
  linear_combination (B^4)*hvalue

#print axioms product_restore_loop_spec

#print axioms mask_words_zero
#print axioms mask_words_full
#print axioms product_restore_loop_unfold
#print axioms product_restore_loop_spec_four
#print axioms product_restore_loop_upper_spec
end UdonVerify.Native
