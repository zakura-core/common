import CommonInversion.Funs
import CommonFG62Arrays

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def inversionRange (start : U32) : core.ops.range.RangeInclusive U32 := ⟨start, 12#u32, false⟩

theorem inversion_range_next_lt (start next : U32) (hs : start.val < 12) (hn : next.val = start.val + 1) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepU32
      (inversionRange start) = ok (some start, inversionRange next) := by
  have hle : start.val ≤ (12#u32).val := by change start.val ≤ 12; omega
  have hlt : start.val < (12#u32).val := by exact hs
  have hfit : start.val + (1#usize).val ≤ UScalar.max .U32 := by
    norm_num [UScalar.max, U32.max, U32.numBits, UScalarTy.numBits]
    omega
  unfold core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
    core.ops.range.RangeInclusive.is_empty
  simp only [inversionRange, core.iter.range.StepU32, core.iter.range.UScalarStep,
    core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.le, core.cmp.impls.PartialOrdU32.lt,
    liftFun2, Bind.bind, Pure.pure, bind_ok, hle, hlt, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  simp only [core.iter.range.UScalarStep.forward_checked, dif_pos hfit, bind_ok]
  congr 1
  congr 1
  congr 1
  apply UScalar.eq_of_val_eq
  simpa only [UScalar.ofNatCore_val_eq, show (1#usize).val = 1 from by decide] using hn.symm

theorem inversion_range_next_last :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepU32
      (inversionRange 12#u32) = ok (some 12#u32, ⟨12#u32, 12#u32, true⟩) := by
  unfold core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
    core.ops.range.RangeInclusive.is_empty
  simp [inversionRange, core.iter.range.StepU32, core.iter.range.UScalarStep,
    core.cmp.PartialOrdU32, core.cmp.impls.PartialOrdU32.le, core.cmp.impls.PartialOrdU32.lt,
    liftFun2, Bind.bind, Pure.pure]

#print axioms inversion_range_next_lt
#print axioms inversion_range_next_last
end UdonVerify.CommonSigned62
