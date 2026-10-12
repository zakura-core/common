import CommonCheckCompareMath

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev CheckRev := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)
def checkRev (endIndex : Usize) : CheckRev := ⟨⟨0#usize, endIndex⟩⟩

theorem check_rev_next_some (endIndex next : Usize) (he : 0 < endIndex.val)
    (hn : next.val = endIndex.val - 1) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) (checkRev endIndex) =
      ok (some next, checkRev next) := by
  apply fg_result_eq
  have hlt : (0#usize).val < endIndex.val := by simpa using he
  have hpositive : (1#usize).val ≤ endIndex.val := by change 1 ≤ endIndex.val; omega
  unfold core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    core.ops.range.Range.Insts.DoubleEndedIterator
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back
  simp only [checkRev, core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, liftFun2, Bind.bind,
    bind_ok, hlt, decide_true, ite_true, core.iter.range.UScalarStep.backward_checked,
    dif_pos hpositive, Std.uncurry_apply_pair, WP.spec_ok]
  have hv : UScalar.ofNatCore (endIndex.val - (1#usize).val)
      (by have := endIndex.hBounds; omega) = next := by
    apply UScalar.eq_of_val_eq
    simpa only [UScalar.ofNatCore_val_eq, show (1#usize).val = 1 from by decide] using hn.symm
  simp only [hv]

theorem check_rev_next_none :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) (checkRev 0#usize) =
      ok (none, checkRev 0#usize) := by
  apply fg_result_eq
  unfold core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    core.ops.range.Range.Insts.DoubleEndedIterator
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back
  simp [checkRev, core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, liftFun2, WP.spec_ok]

theorem check_compare_loop_unfold (iter : CheckRev) (a b : Signed62) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop1 iter a b =
      (do let flow ← CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop1.body iter a b
          match flow with
          | .done result => ok result
          | .cont (next, a1, b1) =>
            CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop1 next a1 b1) := by
  unfold CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62_loop1
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done result => rfl
  | cont state => rcases state with ⟨next, a1, b1⟩; rfl

#print axioms check_rev_next_some
#print axioms check_rev_next_none
#print axioms check_compare_loop_unfold
end UdonVerify.CommonSigned62
