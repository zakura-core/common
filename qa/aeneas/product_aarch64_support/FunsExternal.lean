module
public import NativeField.FunsExternal
public import CommonProductsAarch64.Types
@[expose] public section

open Aeneas Std Result
namespace CommonProductsAarch64

/-- Match the backend string constructor using a kernel proof of its length bound. -/
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by
    simp only [String.size_toByteArray, U32.max, U32.numBits]
    decide +kernel) : Str := Aeneas.Std.toStr s h

def core.cmp.Ordering.is_lt (order : Ordering) : Result Bool :=
  ok (match order with | .lt => true | _ => false)

def core.iter.traits.iterator.Iterator.by_ref.default {Self Item : Type}
    (_inst : Aeneas.Std.core.iter.traits.iterator.Iterator Self Item) (it : Self) :
    Result (Self × (Self → Self)) := ok (it, id)

theorem completeChunksShape {α : Type} (n : Nat) (hn : 0 < n) (xs : List α) :
    (∀ c ∈ (List.toChunksExact n hn xs).1, c.length = n) ∧
      (List.toChunksExact n hn xs).1.length ≤ xs.length := by
  unfold List.toChunksExact
  split_ifs with h
  · simp
  · have ih := completeChunksShape n hn (xs.drop n)
    dsimp only at ih ⊢
    constructor
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [List.length_take]
        omega
      · exact ih.1 c hc
    · simp only [List.length_cons]
      have hdrop : (xs.drop n).length = xs.length - n := List.length_drop
      omega
termination_by xs.length
decreasing_by simp [List.length_drop]; omega

/-- Transparent model of the shared slice partition into full arrays and a tail. -/
def core.slice.Slice.as_chunks {T : Type} (N : Usize) (slice : Aeneas.Std.Slice T) :
    Result (Aeneas.Std.Slice (Array T N) × Aeneas.Std.Slice T) :=
  if hn : 0 < N.val then
    let parts := List.toChunksExact N.val hn slice.val
    let chunks := parts.1.attach.map fun c => Array.from c.val
      ((completeChunksShape N.val hn slice.val).1 c.val c.property)
    ok (Aeneas.Std.Slice.from chunks (by
      have hcount := (completeChunksShape N.val hn slice.val).2
      have hslice := slice.property
      simpa only [chunks, List.length_map, List.length_attach] using _root_.le_trans hcount hslice),
      Aeneas.Std.Slice.from parts.2 (by
        have hrem := List.toChunksExact_remainder_length hn slice.val
        exact _root_.le_trans hrem slice.property))
  else fail .panic

/-- Standard shared chunks, including one final nonempty partial chunk. -/
def core.slice.Slice.chunks {T : Type} (slice : Aeneas.Std.Slice T) (N : Usize) :
    Result (core.slice.iter.Chunks T) :=
  if hn : 0 < N.val then
    let parts := List.toChunksExact N.val hn slice.val
    let full := parts.1.attach.map fun c => Aeneas.Std.Slice.from c.val (by
      have hlen := (completeChunksShape N.val hn slice.val).1 c.val c.property
      have hN := N.hmax
      scalar_tac)
    let tail := Aeneas.Std.Slice.from parts.2 (by
      have hrem := List.toChunksExact_remainder_length hn slice.val
      exact _root_.le_trans hrem slice.property)
    ok ⟨full ++ if parts.2.isEmpty then [] else [tail]⟩
  else fail .panic

def core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    {T : Type} (iter : core.slice.iter.Chunks T) :
    Result (Option (Aeneas.Std.Slice T) × core.slice.iter.Chunks T) :=
  match iter.chunks with
  | [] => ok (none,iter)
  | first::rest => ok (some first,⟨rest⟩)

end CommonProductsAarch64
