import NativeProductFoldLoops
open Aeneas Std Result
namespace UdonVerify.Native
set_option maxHeartbeats 200000
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem fold_correction_bind_eq {T : Type} (a : A8) (correction : A4) (k : A8 → Result T) :
    (Std.bind (core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice U64)) a {start:=1#usize,«end»:=5#usize})
      (Std.uncurry fun s ib =>
        Std.bind (core.slice.Slice.iter_mut s) (Std.uncurry fun im itb =>
          Std.bind (mutableZipCtor
            (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
            (NativeField.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter U64 4#usize) im correction)
            (Std.uncurry fun it zb =>
              Std.bind (NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow_loop0
                ib itb zb it (fun z=>z) 0#u64) k)))) = (do let out ← foldCorrection a correction; k out) := by
  unfold foldCorrection
  simp only [Std.bind_assoc,Std.uncurry]
  with_unfolding_all rfl

#print axioms fold_correction_bind_eq
end UdonVerify.Native
