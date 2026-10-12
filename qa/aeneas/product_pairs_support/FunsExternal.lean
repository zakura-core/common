module
public import NativeField.FunsExternal
public import CommonProductPairs.Types
@[expose] public section

open Aeneas Std Result
namespace CommonProductPairs

/-- Match the backend string constructor using a kernel proof of its length bound. -/
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by
    simp only [String.size_toByteArray, U32.max, U32.numBits]
    decide +kernel) : Str := Aeneas.Std.toStr s h

def core.cmp.Ordering.is_lt (order : Ordering) : Result Bool :=
  ok (match order with | .lt => true | _ => false)

def core.iter.traits.iterator.Iterator.by_ref.default {Self Item : Type}
    (_inst : Aeneas.Std.core.iter.traits.iterator.Iterator Self Item) (it : Self) :
    Result (Self × (Self → Self)) := ok (it, id)

end CommonProductPairs
