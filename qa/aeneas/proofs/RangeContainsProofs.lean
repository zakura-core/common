import SqrtSupport.RangeContains
open Aeneas Std Result
namespace UdonVerify.Sqrt
theorem range_check_eq (n : U32) (hl : 1 ≤ n.val) (hr : n.val ≤ 64) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU32
      core.cmp.PartialOrdU32 core.cmp.PartialOrdU32 ⟨1#u32,64#u32,false⟩ n = ok true := by
  simp [core.ops.range.RangeInclusive.contains,core.cmp.PartialOrdU32,
    core.cmp.impls.PartialOrdU32.le,liftFun2,hl,hr]
end UdonVerify.Sqrt
