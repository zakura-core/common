import CommonProductPairsPortableBridges
import CommonProductPortablePrimitives
import NativeProductFold
open Aeneas Std Result
open CommonProductPairs.field.pasta.products.ProductSum
namespace UdonVerify.ProductPairs
open UdonVerify.Native UdonVerify.ProductPortable
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2048
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
abbrev FoldZip := core.iter.adapters.zip.Zip (core.slice.iter.IterMut U64)
  (core.array.iter.IntoIter U64 4#usize)

theorem pairs_fold_loop0_unfold (it : FoldZip) (back : FoldZip → FoldZip) (carry : U64) :
    fold_overflow_loop0 it back carry = (do
      let r ← fold_overflow_loop0.body it back carry
      match r with
      | .done out => ok out
      | .cont (i,b,c) => fold_overflow_loop0 i b c) := by
  unfold fold_overflow_loop0
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨i,b,c⟩; rfl

theorem pairs_fold_tail_bridge :
    @CommonProductPairs.field.pasta.products.ProductSum.fold_overflow_loop1 =
    @NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow_loop0_loop0 := by rfl

/-- The exact iterator setup from the production overflow folding path. -/
def pairsFoldCorrection (a : A8) (correction : A4) : Result A8 := do
  let (s,ib) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U64)) a {start:=1#usize,«end»:=5#usize}
  let (im,itb) ← core.slice.Slice.iter_mut s
  let (it,zb) ← mutableZipCtor
    (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
    (CommonProductPairs.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter U64 4#usize) im correction
  let (carry, back) ← fold_overflow_loop0 it (fun z=>z) 0#u64
  let a2 := ib (itb (zb back))
  let (s2, ib1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeFromUsizeSlice U64)) a2 {start:=5#usize}
  let (it1, intoBack) ← MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter s2
  let (carry1, im2, back1) ← fold_overflow_loop1 it1 (fun im=>im) carry
  massert (carry1 = 0#u64)
  ok (ib1 (intoBack (back1 im2)))

attribute [local irreducible] NativeField.zakura_udon.field.pasta.word.adc
  NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow_loop0_loop0

theorem pairs_fold_correction_eq_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 : U64) :
    pairsFoldCorrection (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7]) (Array.make 4#usize [b0,b1,b2,b3]) =
    Native.foldCorrection (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7]) (Array.make 4#usize [b0,b1,b2,b3]) := by
  unfold pairsFoldCorrection Native.foldCorrection
  rw [pairs_fold_tail_bridge]
  simp [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.iter_mut, mutableZipCtor,
    CommonProductPairs.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter,
    NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter,
    _root_.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    Array.to_slice_mut,Array.to_slice,Std.bind_assoc]
  rw [pairs_fold_loop0_unfold,Native.fold_loop0_unfold]
  unfold fold_overflow_loop0.body NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,Std.bind_assoc]
  rw [UdonVerify.ProductPairs.PortableBridge.field.pasta.word.adc, portable_adc_bridge]
  apply congrArg (fun k : U64 × U64 → Result A8 =>
    Std.bind (NativeField.zakura_udon.field.pasta.word.adc (Slice.from [a1,a2,a3,a4] (by scalar_tac))[0] (Slice.from [b0,b1,b2,b3] (by scalar_tac))[0] 0#u64) k)
  funext pair0
  rcases pair0 with ⟨r0,c0⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [pairs_fold_loop0_unfold,Native.fold_loop0_unfold]
  unfold fold_overflow_loop0.body NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,Std.bind_assoc]
  rw [UdonVerify.ProductPairs.PortableBridge.field.pasta.word.adc, portable_adc_bridge]
  apply congrArg (fun k : U64 × U64 → Result A8 =>
    Std.bind (NativeField.zakura_udon.field.pasta.word.adc (Slice.from [a1,a2,a3,a4] (by scalar_tac))[1] (Slice.from [b0,b1,b2,b3] (by scalar_tac))[1] c0) k)
  funext pair1
  rcases pair1 with ⟨r1,c1⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [pairs_fold_loop0_unfold,Native.fold_loop0_unfold]
  unfold fold_overflow_loop0.body NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,Std.bind_assoc]
  rw [UdonVerify.ProductPairs.PortableBridge.field.pasta.word.adc, portable_adc_bridge]
  apply congrArg (fun k : U64 × U64 → Result A8 =>
    Std.bind (NativeField.zakura_udon.field.pasta.word.adc (Slice.from [a1,a2,a3,a4] (by scalar_tac))[2] (Slice.from [b0,b1,b2,b3] (by scalar_tac))[2] c1) k)
  funext pair2
  rcases pair2 with ⟨r2,c2⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [pairs_fold_loop0_unfold,Native.fold_loop0_unfold]
  unfold fold_overflow_loop0.body NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,Std.bind_assoc]
  rw [UdonVerify.ProductPairs.PortableBridge.field.pasta.word.adc, portable_adc_bridge]
  apply congrArg (fun k : U64 × U64 → Result A8 =>
    Std.bind (NativeField.zakura_udon.field.pasta.word.adc (Slice.from [a1,a2,a3,a4] (by scalar_tac))[3] (Slice.from [b0,b1,b2,b3] (by scalar_tac))[3] c2) k)
  funext pair3
  rcases pair3 with ⟨r3,c3⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [pairs_fold_loop0_unfold,Native.fold_loop0_unfold]
  unfold fold_overflow_loop0.body NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow_loop0.body
  simp [mutableZipNext,core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next,core.slice.iter.IteratorSliceIter.next,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    Array.to_slice_mut,Array.to_slice,Array.from_slice,Slice.setAtNat,Std.bind_assoc]

  apply congrArg (Std.bind _)
  funext result
  rcases result with ⟨carry,it,back⟩
  simp only [Std.uncurry,Std.bind_assoc,bind_ok]


/-- The sequential-loop extraction and the earlier fused-loop extraction execute identically. -/
theorem pairs_fold_correction_eq (a : A8) (correction : A4) :
    pairsFoldCorrection a correction = Native.foldCorrection a correction := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,ha⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : U64,
      a=Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7] :=
    ⟨a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,a[7]!,Native.array_eight_eta a⟩
  obtain ⟨b0,b1,b2,b3,hb⟩ : ∃ b0 b1 b2 b3 : U64,
      correction=Array.make 4#usize [b0,b1,b2,b3] :=
    ⟨correction[0]!,correction[1]!,correction[2]!,correction[3]!,CommonVerify.array_four_eta correction⟩
  subst a correction
  exact pairs_fold_correction_eq_eight _ _ _ _ _ _ _ _ _ _ _ _

@[step]
theorem pairs_fold_correction_spec (a : A8) (correction : A4)
    (hbound : val8 a+B*val4 correction<R^2) :
    pairsFoldCorrection a correction ⦃ out=>val8 out=val8 a+B*val4 correction ⦄ := by
  rw [pairs_fold_correction_eq]
  exact Native.fold_correction_spec a correction hbound

#print axioms pairs_fold_loop0_unfold
#print axioms pairs_fold_tail_bridge
#print axioms pairs_fold_correction_eq_eight
#print axioms pairs_fold_correction_eq
#print axioms pairs_fold_correction_spec
end UdonVerify.ProductPairs
