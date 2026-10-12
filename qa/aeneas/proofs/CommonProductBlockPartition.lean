import CommonProductBlockTail
import CommonProductChunkMath

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem as_chunks_four_spec {α : Type} (xs : Aeneas.Std.Slice α) :
    CommonProductsAarch64.core.slice.Slice.as_chunks 4#usize xs ⦃ chunks rem =>
      (chunks.val.map (fun a => a.val)).flatten ++ rem.val = xs.val ∧
        chunks.length = xs.length / 4 ∧ rem.length = xs.length % 4 ⦄ := by
  have h := four_chunks_partition xs.val
  unfold CommonProductsAarch64.core.slice.Slice.as_chunks
  simp only [show 0 < (4#usize).val from by decide,_root_.dite_true,WP.spec_ok]
  with_unfolding_all
    simp only [WP.uncurry',Aeneas.Std.Slice.from_val,Aeneas.Std.Slice.length,Array.from_val,
      List.map_map,Function.comp_def,List.attach_map_subtype_val,List.attach_map_val,
      List.map_id,List.length_map,List.length_attach]
    simpa only [show (4#usize).val = 4 from rfl] using
      (And.intro h.1 (And.intro h.2.2.2.1 h.2.2.2.2))

theorem quad_sum_flatten {M S T : Type} (li ri : Usize)
    (lhs : List (Quad M S)) (rhs : List (Quad M T))
    (a : List (Element M S)) (b : List (Element M T)) (hlen : lhs.length = rhs.length) :
    quadSum li ri lhs rhs + wordDot (fun x => x.limbs) (fun y => y.limbs) li.val ri.val a b =
      wordDot (fun x => x.limbs) (fun y => y.limbs) li.val ri.val
        ((lhs.map (fun q => q.val)).flatten ++ a) ((rhs.map (fun q => q.val)).flatten ++ b) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> simp_all [quadSum,wordDot,rawSum]
  | cons x xs ih =>
    cases rhs with
    | nil => simp at hlen
    | cons y ys =>
      have htail := ih ys (by simpa using hlen)
      simp only [quadSum,quadValue,wordDot,List.map_cons,List.flatten_cons,List.append_assoc]
      rw [raw_sum_append _ _ x.val _ y.val _ (by simp)]
      dsimp only [wordDot] at htail
      omega

/-- Both native loops account for the complete source slices, including the tail. -/
@[step]
theorem accumulate_column_spec {M S T : Type} (li ri : Usize) (hi : li.val < 4) (hj : ri.val < 4)
    (columns : BatchColumns) (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length)
    (hbound : batchColumnsInteger columns + wordDot (fun a => a.limbs) (fun b => b.limbs)
      li.val ri.val lhs.val rhs.val < B ^ 3) :
    accumulateColumn li ri columns lhs rhs ⦃ out =>
      batchColumnsInteger out = batchColumnsInteger columns + wordDot
        (fun a => a.limbs) (fun b => b.limbs) li.val ri.val lhs.val rhs.val ⦄ := by
  unfold accumulateColumn
  step -grind with (as_chunks_four_spec lhs) as ⟨lq,lr,hlpartition,hlcount,hlrem⟩
  step -grind with (as_chunks_four_spec rhs) as ⟨rq,rr,hrpartition,hrcount,hrrem⟩
  have hq : lq.length = rq.length := by omega
  have hrem : lr.length = rr.length := by omega
  have hsplit := quad_sum_flatten li ri lq.val rq.val lr.val rr.val hq
  rw [hlpartition,hrpartition] at hsplit
  have hquad : batchColumnsInteger columns + quadSum li ri lq.val rq.val < B ^ 3 := by omega
  simp only [core.slice.Slice.iter,core.iter.traits.iterator.Iterator.zip.trait_default,
    core.iter.traits.iterator.Iterator.zip.default,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  step -grind with (quad_accumulation_spec li ri hi hj lq rq columns hq hquad) as ⟨out,hout⟩
  step -grind with (tail_accumulation_spec li ri hi hj lr rr out hrem (by omega)) as ⟨final,hfinal⟩
  omega

#print axioms as_chunks_four_spec
#print axioms quad_sum_flatten
#print axioms accumulate_column_spec
end UdonVerify.ProductBlock
