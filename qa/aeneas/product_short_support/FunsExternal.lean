module
public import NativeField.FunsExternal
public import CommonProductShort.Types
@[expose] public section

open Aeneas Std Result
namespace CommonProductShort

/-- Match the backend string constructor using a kernel proof of its length bound. -/
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by
    simp only [String.size_toByteArray, U32.max, U32.numBits]
    decide +kernel) : Str := Aeneas.Std.toStr s h

def core.cmp.Ordering.is_lt (order : Ordering) : Result Bool :=
  ok (match order with | .lt => true | _ => false)

def core.iter.traits.iterator.Iterator.by_ref.default {Self Item : Type}
    (_inst : Aeneas.Std.core.iter.traits.iterator.Iterator Self Item) (it : Self) :
    Result (Self × (Self → Self)) := ok (it, id)

/-- The standard shared-slice partition into complete arrays and a remainder. -/
def core.slice.Slice.as_chunks {T : Type} (N : Usize) (slice : Aeneas.Std.Slice T) :
    Result (Aeneas.Std.Slice (Array T N) × Aeneas.Std.Slice T) := do
  massert (N.val ≠ 0)
  let count := slice.length / N.val
  let chunks : List (Array T N) := List.ofFn (fun (i : Fin count) =>
    Array.from (slice.val.drop (i.val * N.val) |>.take N.val) (by
      have hcount : count * N.val ≤ slice.length := Nat.div_mul_le_self _ _
      have hi : i.val + 1 ≤ count := i.isLt
      have hmul := Nat.mul_le_mul_right N.val hi
      change count * N.val ≤ slice.val.length at hcount
      simp only [Nat.add_mul, Nat.one_mul] at hmul
      simp only [List.length_take, List.length_drop]
      omega))
  let complete := Aeneas.Std.Slice.from chunks (by
    have hcount := Nat.div_le_self slice.length N.val
    have hslice := slice.property
    simpa only [chunks, List.length_ofFn] using _root_.le_trans hcount hslice)
  let remainder := Aeneas.Std.Slice.from (slice.val.drop (count * N.val)) (by
    have hslice := slice.property
    simp only [List.length_drop]
    omega)
  ok (complete, remainder)

end CommonProductShort
