import Parameters

open Aeneas Std Result
open udon_kernel_slice.field.pasta

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def digits4 (a b c d : U64) : Nat := a.val + B*b.val + B^2*c.val + B^3*d.val

theorem digits4_lt (a b c d : U64) : digits4 a b c d < R := by
  unfold digits4 R B
  scalar_tac

theorem cancel_low (x p inv : Nat) (hinv : (p*inv+1)%B = 0) :
    (x + ((x*inv)%B)*p)%B = 0 := by
  have heq : (x + ((x*inv)%B)*p)%B = (x*(p*inv+1))%B := by
    conv_rhs => rw [show x*(p*inv+1) = x+x*inv*p by ring]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  rw [heq, Nat.mul_mod, hinv]
  simp

theorem shift62_split (a : U64) :
    (a.val * 2^62)%B + B*(a.val/4) = a.val * 2^62 := by
  have h := Nat.mod_add_div a.val 4
  have hm := Nat.mul_mod_mul_left (2^62) a.val 4
  norm_num [B] at hm ⊢
  rw [Nat.mul_comm (4611686018427387904 : Nat) a.val] at hm
  rw [hm]
  omega

abbrev range32 (n : I32) : core.ops.range.Range I32 := { start := n, «end» := 4#i32 }

theorem next_i32_0 : core.iter.range.IteratorRange.next core.iter.range.StepI32 (range32 0#i32) =
    ok (some 0#i32, range32 1#i32) := by
  simp [range32, core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.iter.range.IScalarStep.forward_checked,
    IScalar.max, IScalarTy.numBits, I32.max, I32.numBits, core.cmp.impls.PartialOrdI32.lt]

theorem next_i32_1 : core.iter.range.IteratorRange.next core.iter.range.StepI32 (range32 1#i32) =
    ok (some 1#i32, range32 2#i32) := by
  simp [range32, core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.iter.range.IScalarStep.forward_checked,
    IScalar.max, IScalarTy.numBits, I32.max, I32.numBits, core.cmp.impls.PartialOrdI32.lt]

theorem next_i32_2 : core.iter.range.IteratorRange.next core.iter.range.StepI32 (range32 2#i32) =
    ok (some 2#i32, range32 3#i32) := by
  simp [range32, core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.iter.range.IScalarStep.forward_checked,
    IScalar.max, IScalarTy.numBits, I32.max, I32.numBits, core.cmp.impls.PartialOrdI32.lt]

theorem next_i32_3 : core.iter.range.IteratorRange.next core.iter.range.StepI32 (range32 3#i32) =
    ok (some 3#i32, range32 4#i32) := by
  simp [range32, core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.iter.range.IScalarStep.forward_checked,
    IScalar.max, IScalarTy.numBits, I32.max, I32.numBits, core.cmp.impls.PartialOrdI32.lt]

theorem next_i32_4 : core.iter.range.IteratorRange.next core.iter.range.StepI32 (range32 4#i32) =
    ok (none, range32 4#i32) := by
  simp [range32, core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.cmp.impls.PartialOrdI32.lt]

end UdonVerify
