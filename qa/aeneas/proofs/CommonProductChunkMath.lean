import CommonProductSliceMath

open Aeneas Std Result
namespace UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Partition facts for the same standard-library list model used by Aeneas. -/
theorem four_chunks_partition {α : Type} (xs : List α) :
    let split := List.toChunksExact 4 (by decide) xs
    split.1.flatten ++ split.2 = xs ∧
      (∀ chunk ∈ split.1, chunk.length = 4) ∧ split.2.length < 4 ∧
      split.1.length = xs.length / 4 ∧ split.2.length = xs.length % 4 := by
  unfold List.toChunksExact
  split_ifs with h
  · simp only [List.flatten_nil, List.nil_append, List.not_mem_nil, false_implies, forall_const,
      true_and, List.length_nil]
    exact ⟨h, by omega, by omega⟩
  · have ih := four_chunks_partition (xs.drop 4)
    dsimp only at ih ⊢
    have htake : (xs.take 4).length = 4 := by simp [List.length_take]; omega
    have hdrop : (xs.drop 4).length = xs.length - 4 := List.length_drop
    refine ⟨?_, ?_, ih.2.2.1, ?_, ?_⟩
    · simpa only [List.flatten_cons, List.append_assoc, ih.1] using List.take_append_drop 4 xs
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

@[step]
theorem chunks_exact_four_spec {α : Type} (xs : Aeneas.Std.Slice α) :
    core.slice.Slice.chunks_exact xs 4#usize ⦃ it =>
      (it.chunks.map (fun s => s.val)).flatten ++ it.remainder.val = xs.val ∧
      (∀ chunk ∈ it.chunks, chunk.length = 4) ∧ it.remainder.length < 4 ∧
      it.chunks.length = xs.length / 4 ∧ it.remainder.length = xs.length % 4 ⦄ := by
  have h := four_chunks_partition xs.val
  unfold core.slice.Slice.chunks_exact
  simp only [show (4#usize).val = 4 from rfl, show 4 > 0 from by decide, _root_.dite_true, WP.spec_ok]
  simp only [List.map_map, Function.comp_def, Aeneas.Std.Slice.length, Aeneas.Std.Slice.from_val,
    List.attach_map_subtype_val, List.attach_map_val, List.map_id, List.length_map, List.length_attach]
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  intro chunk hchunk
  rcases List.mem_map.mp hchunk with ⟨source, hsource, rfl⟩
  simpa only [Aeneas.Std.Slice.length, Aeneas.Std.Slice.from_val] using h.2.1 source.val source.property

/-- Raw products grouped into paired chunks, without reducing intermediate sums. -/
def chunkSum {α β : Type} (left : α → Nat) (right : β → Nat) :
    List (Aeneas.Std.Slice α) → List (Aeneas.Std.Slice β) → Nat
  | a :: xs, b :: ys => rawSum left right a.val b.val + chunkSum left right xs ys
  | _, _ => 0

theorem chunk_sum_flatten {α β : Type} (left : α → Nat) (right : β → Nat)
    (lhs : List (Aeneas.Std.Slice α)) (rhs : List (Aeneas.Std.Slice β))
    (a : List α) (b : List β) (hlen : lhs.length = rhs.length)
    (ha : ∀ x ∈ lhs, x.length = 4) (hb : ∀ y ∈ rhs, y.length = 4) :
    chunkSum left right lhs rhs + rawSum left right a b =
      rawSum left right ((lhs.map (fun s => s.val)).flatten ++ a)
        ((rhs.map (fun s => s.val)).flatten ++ b) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> simp_all [chunkSum, rawSum]
  | cons x xs ih =>
    cases rhs with
    | nil => simp at hlen
    | cons y ys =>
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      have htail := ih ys (by simpa using hlen)
        (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz]))
      simp only [chunkSum, List.map_cons, List.flatten_cons, List.append_assoc]
      rw [raw_sum_append left right x.val _ y.val _ (by change x.length = y.length; omega)]
      omega

/-- Advancing a read-only exact-chunk iterator preserves its observable remainder. -/
@[step]
theorem chunks_next_remainder {α : Type} (it : core.slice.iter.ChunksExact α) :
    core.slice.iter.IteratorChunksExact.next it ⦃ out => out.2.remainder = it.remainder ⦄ := by
  unfold core.slice.iter.IteratorChunksExact.next
  cases it.chunks <;> simp [WP.spec_ok]

/-- The remainder frame is valid after any number of paired chunk advances. -/
theorem chunk_pair_advance_remainder {α β : Type}
    (lhs : core.slice.iter.ChunksExact α) (rhs : core.slice.iter.ChunksExact β) (n : Nat) :
    core.slice.iter.ChunksExact.getRemainder { lhs with chunks := lhs.chunks.drop n } =
      core.slice.iter.ChunksExact.getRemainder lhs ∧
    core.slice.iter.ChunksExact.getRemainder { rhs with chunks := rhs.chunks.drop n } =
      core.slice.iter.ChunksExact.getRemainder rhs := by
  exact ⟨rfl,rfl⟩

#print axioms four_chunks_partition
#print axioms chunks_exact_four_spec
#print axioms chunk_sum_flatten
#print axioms chunks_next_remainder
#print axioms chunk_pair_advance_remainder
end UdonVerify.Products
