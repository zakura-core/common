import NativeProductFoldTail
open Aeneas Std Result
open NativeField.zakura_udon.field.pasta.products.ProductSum
namespace UdonVerify.Native
set_option maxHeartbeats 300000
set_option maxRecDepth 2048
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
abbrev FoldZip := core.iter.adapters.zip.Zip (core.slice.iter.IterMut U64)
  (core.array.iter.IntoIter U64 4#usize)

theorem fold_loop0_unfold (ib : Aeneas.Std.Slice U64 → A8)
    (itb : core.slice.iter.IterMut U64 → Aeneas.Std.Slice U64)
    (zb : FoldZip → core.slice.iter.IterMut U64)
    (it : FoldZip) (back : FoldZip → FoldZip) (carry : U64) :
    fold_overflow_loop0 ib itb zb it back carry = (do
      let r ← fold_overflow_loop0.body ib itb zb it back carry
      match r with
      | .done out => ok out
      | .cont (i,b,c) => fold_overflow_loop0 ib itb zb i b c) := by
  unfold fold_overflow_loop0
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨i,b,c⟩; rfl

/-- The exact iterator setup from the production overflow folding path. -/
def foldCorrection (a : A8) (correction : A4) : Result A8 := do
  let (s,ib) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U64)) a {start:=1#usize,«end»:=5#usize}
  let (im,itb) ← core.slice.Slice.iter_mut s
  let (it,zb) ← mutableZipCtor
    (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
    (NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter U64 4#usize) im correction
  fold_overflow_loop0 ib itb zb it (fun z=>z) 0#u64

@[step]
theorem fold_correction_spec_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 : U64)
    (hbound : val8 (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])+
      B*val4 (Array.make 4#usize [b0,b1,b2,b3]) < R^2) :
    foldCorrection (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])
      (Array.make 4#usize [b0,b1,b2,b3])
      ⦃ out => val8 out = val8 (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])+
        B*val4 (Array.make 4#usize [b0,b1,b2,b3]) ⦄ := by
  unfold foldCorrection
  simp [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.iter_mut, mutableZipCtor,
    NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter,
    _root_.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    Array.to_slice_mut,Array.to_slice,Std.bind_assoc]
  rw [fold_loop0_unfold]
  unfold fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair0,h0⟩
  rcases pair0 with ⟨r0,c0⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [fold_loop0_unfold]
  unfold fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair1,h1⟩
  rcases pair1 with ⟨r1,c1⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [fold_loop0_unfold]
  unfold fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair2,h2⟩
  rcases pair2 with ⟨r2,c2⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [fold_loop0_unfold]
  unfold fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair3,h3⟩
  rcases pair3 with ⟨r3,c3⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [fold_loop0_unfold]
  unfold fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    Array.to_slice_mut,Array.to_slice,Array.from_slice,Slice.setAtNat,Std.bind_assoc]
  have hsplice := fold_splice_eight a0 a1 a2 a3 a4 a5 a6 a7 r0 r1 r2 r3
  simp only [hsplice]
  simp only [slice_eight_drop_five]
  step -grind with (fold_tail_spec a5 a6 a7 c3) as ⟨result,hcarry,hlen,htail⟩
  rcases result with ⟨carry,it,back⟩
  simp only [Std.uncurry,bind_ok] at hcarry hlen htail ⊢
  change r0.val+B*c0.val=a1.val+b0.val+0 at h0
  change r1.val+B*c1.val=a2.val+b1.val+c0.val at h1
  change r2.val+B*c2.val=a3.val+b2.val+c1.val at h2
  change r3.val+B*c3.val=a4.val+b3.val+c2.val at h3
  have hweighted :
      a0.val+B*r0.val+B^2*r1.val+B^3*r2.val+B^4*r3.val+
        B^5*val3 (back it).slice+R^2*carry.val =
      val8 (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])+
        B*val4 (Array.make 4#usize [b0,b1,b2,b3]) := by
    simp only [val8,val4,Array.getElem!_Nat_eq,Array.make_val]
    simp only [List.getElem!_cons_zero,List.getElem!_cons_succ]
    unfold R
    linear_combination B*h0+B^2*h1+B^3*h2+B^4*h3+B^5*htail
  have hc : carry.val=0 := by
    have hpos : 0<R^2 := by norm_num [R,B]
    nlinarith only [hweighted,hbound,hpos]
  have hcz : carry=0#u64 := by scalar_tac
  rw [hcz]
  step -grind
  with_unfolding_all rw [tail_splice_value _ _ _ _ _ _ _ _ _ hlen]
  simpa only [hc,Nat.mul_zero,Nat.add_zero] using hweighted

@[step]
theorem fold_correction_spec (a : A8) (correction : A4)
    (hbound : val8 a+B*val4 correction<R^2) :
    foldCorrection a correction ⦃ out=>val8 out=val8 a+B*val4 correction ⦄ := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,ha⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : U64,
      a=Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7] :=
    ⟨a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,a[7]!,array_eight_eta a⟩
  obtain ⟨b0,b1,b2,b3,hb⟩ : ∃ b0 b1 b2 b3 : U64,
      correction=Array.make 4#usize [b0,b1,b2,b3] :=
    ⟨correction[0]!,correction[1]!,correction[2]!,correction[3]!,CommonVerify.array_four_eta correction⟩
  subst a correction
  exact fold_correction_spec_eight _ _ _ _ _ _ _ _ _ _ _ _ hbound

#print axioms fold_loop0_unfold
#print axioms fold_correction_spec_eight
#print axioms fold_correction_spec
end UdonVerify.Native
