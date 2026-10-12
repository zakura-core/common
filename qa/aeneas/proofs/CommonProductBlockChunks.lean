import CommonProductBlockPartition

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Partition facts for the same standard-library list model used by Aeneas. -/
theorem thirty_two_chunks_partition {α : Type} (xs : List α) :
    let split := List.toChunksExact 32 (by decide) xs
    split.1.flatten ++ split.2 = xs ∧
      (∀ chunk ∈ split.1, chunk.length = 32) ∧ split.2.length < 32 ∧
      split.1.length = xs.length / 32 ∧ split.2.length = xs.length % 32 := by
  unfold List.toChunksExact
  split_ifs with h
  · simp only [List.flatten_nil, List.nil_append, List.not_mem_nil, false_implies, forall_const,
      true_and, List.length_nil]
    exact ⟨h, by omega, by omega⟩
  · have ih := thirty_two_chunks_partition (xs.drop 32)
    dsimp only at ih ⊢
    have htake : (xs.take 32).length = 32 := by simp [List.length_take]; omega
    have hdrop : (xs.drop 32).length = xs.length - 32 := List.length_drop
    refine ⟨?_, ?_, ih.2.2.1, ?_, ?_⟩
    · simpa only [List.flatten_cons, List.append_assoc, ih.1] using List.take_append_drop 32 xs
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact htake
      · exact ih.2.1 c hc
    · simp only [List.length_cons]
      have hcount := ih.2.2.2.1
      omega
    · have hrem := ih.2.2.2.2
      omega
termination_by xs.length
decreasing_by simp [List.length_drop]; omega

theorem map_uniform_lengths {α : Type} (f : α → Nat) (xs : List α) (n : Nat)
    (h : ∀ x ∈ xs, f x = n) : xs.map f = List.replicate xs.length n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.length_cons,List.replicate_succ]
    rw [h x (by simp), ih (fun a ha => h a (by simp [ha]))]

abbrev BlockChunks (α : Type) := CommonProductsAarch64.core.slice.iter.Chunks α

/-- The public chunk iterator includes every element and exactly one partial tail. -/
@[step]
theorem chunks_thirty_two_spec {α : Type} (xs : Aeneas.Std.Slice α) :
    CommonProductsAarch64.core.slice.Slice.chunks xs 32#usize ⦃ out =>
      (out.chunks.map (fun a => a.val)).flatten = xs.val ∧
      (∀ chunk ∈ out.chunks, chunk.length ≤ 32) ∧
      out.chunks.map (fun a => a.length) = List.replicate (xs.length / 32) 32 ++
        (if xs.length % 32 = 0 then [] else [xs.length % 32]) ⦄ := by
  have h := thirty_two_chunks_partition xs.val
  let parts := List.toChunksExact 32 (by decide) xs.val
  let full : List (Aeneas.Std.Slice α) := parts.1.attach.map fun c =>
    Aeneas.Std.Slice.from c.val (by
      have hlen := h.2.1 c.val c.property
      scalar_tac)
  let tail := Aeneas.Std.Slice.from parts.2 (by
    have hrem := List.toChunksExact_remainder_length (show 0 < 32 from by decide) xs.val
    exact _root_.le_trans hrem xs.property)
  have hfull : ∀ c ∈ full, c.length = 32 := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨source,hsource,rfl⟩
    simpa only [Aeneas.Std.Slice.length,Aeneas.Std.Slice.from_val] using h.2.1 source.val source.property
  have hfullCount : full.length = xs.length / 32 := by
    simpa only [full,List.length_map,List.length_attach] using h.2.2.2.1
  have htailCount : tail.length = xs.length % 32 := by
    simpa only [tail,parts,Aeneas.Std.Slice.length,Aeneas.Std.Slice.from_val] using h.2.2.2.2
  have htailBound : tail.length < 32 := by
    simpa only [tail,parts,Aeneas.Std.Slice.length,Aeneas.Std.Slice.from_val] using h.2.2.1
  have hpartsLength : parts.2.length = tail.length := by
    simp only [tail,Aeneas.Std.Slice.length,Aeneas.Std.Slice.from_val]
  have hpartition : (full.map (fun c => c.val)).flatten ++ tail.val = xs.val := by
    simpa only [full,tail,parts,Aeneas.Std.Slice.from_val,List.map_map,Function.comp_def,
      List.attach_map_subtype_val,List.attach_map_val,List.map_id] using h.1
  have hlengths := map_uniform_lengths (fun a : Aeneas.Std.Slice α => a.length) full 32 hfull
  rw [hfullCount] at hlengths
  have hmodel : CommonProductsAarch64.core.slice.Slice.chunks xs 32#usize =
      ok (⟨full ++ if parts.2.isEmpty then [] else [tail]⟩ : BlockChunks α) := by
    unfold CommonProductsAarch64.core.slice.Slice.chunks
    rw [dif_pos (show 0 < (32#usize).val from by decide)]
    with_unfolding_all rfl
  rw [hmodel]
  simp only [WP.spec_ok]
  by_cases hempty : parts.2 = []
  · have hzero : tail.val = [] := by simpa only [tail,Aeneas.Std.Slice.from_val] using hempty
    have hmod : xs.length % 32 = 0 := by
      have hz : tail.length = 0 := by simp [Aeneas.Std.Slice.length,hzero]
      omega
    simp only [hempty,List.isEmpty_nil,↓reduceIte,List.append_nil,hmod]
    refine ⟨?_,?_,hlengths⟩
    · simpa only [hzero,List.append_nil] using hpartition
    · intro c hc
      exact Nat.le_of_eq (hfull c hc)
  · have hnonzero : xs.length % 32 ≠ 0 := by
      intro hz
      have hlen : parts.2.length = 0 := by rw [hpartsLength]; omega
      exact hempty (List.eq_nil_of_length_eq_zero hlen)
    have hnotEmpty : parts.2.isEmpty = false := List.isEmpty_eq_false_iff.mpr hempty
    simp only [hnotEmpty,Bool.false_eq_true,↓reduceIte,hnonzero,List.map_append,
      List.map_cons,List.map_nil,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
    refine ⟨hpartition,?_,?_⟩
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact Nat.le_of_eq (hfull c hc)
      · have hc' : c = tail := List.mem_singleton.mp hc
        subst c
        exact Nat.le_of_lt htailBound
    · rw [hlengths,htailCount]

#print axioms thirty_two_chunks_partition
#print axioms map_uniform_lengths
#print axioms chunks_thirty_two_spec
end UdonVerify.ProductBlock
