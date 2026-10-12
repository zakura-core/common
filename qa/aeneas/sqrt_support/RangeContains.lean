module
public import Aeneas
@[expose] public section
open Aeneas Std Result
namespace Aeneas.Std
/-- Inclusive lower bound; exhausted ranges have an exclusive equal upper bound. -/
def core.ops.range.RangeInclusive.contains {Idx U : Type}
    (_same : core.cmp.PartialOrd Idx Idx)
    (left : core.cmp.PartialOrd Idx U) (right : core.cmp.PartialOrd U Idx)
    (range : core.ops.range.RangeInclusive Idx) (item : U) : Result Bool := do
  let lower ← left.le range.start item
  if lower then
    if range.exhausted then right.lt item range.start else right.le item range.«end»
  else ok false
end Aeneas.Std
