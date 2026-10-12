import NativeRepresentation

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem and_power_bit (a k : Nat) :
    a &&& 2^k = if a/2^k%2=1 then 2^k else 0 := by
  split_ifs with hbit
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : k=i
    · subst i
      simp only [Nat.testBit_two_pow_self,Bool.and_true]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp [hbit]
    · simp only [Nat.testBit_two_pow_of_ne hi,Bool.and_false]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : k=i
    · subst i
      simp only [Nat.testBit_two_pow_self,Bool.and_true,Nat.testBit_zero]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp [hbit]
    · simp only [Nat.testBit_two_pow_of_ne hi,Bool.and_false]
      simp

theorem prefix_step (a k : Nat) :
    a/2^k=2*(a/2^(k+1))+a/2^k%2 := by
  have h := Nat.mod_add_div (a/2^k) 2
  rw [Nat.div_div_eq_div_mul,←pow_succ] at h
  omega

theorem leading_zeros_nonzero (exponent : U64) (hne : exponent.val≠0) :
    (core.num.U64.leading_zeros exponent).val=64-Nat.log 2 exponent.val-1 := by
  have hneBV : exponent.bv≠0 := by
    intro h
    apply hne
    exact congrArg BitVec.toNat h
  unfold core.num.U64.leading_zeros
  change (BitVec.leadingZeros exponent.bv)%2^32=64-Nat.log 2 exponent.val-1
  unfold BitVec.leadingZeros
  rw [if_neg hneBV]
  change (64-Nat.log 2 exponent.val-1)%2^32=64-Nat.log 2 exponent.val-1
  apply Nat.mod_eq_of_lt
  omega

theorem highest_bit_spec (exponent : U64) (hne : exponent.val≠0) :
    Nat.log 2 exponent.val<64 ∧ exponent.val/2^(Nat.log 2 exponent.val)=1 := by
  have hlt : Nat.log 2 exponent.val<64 := Nat.log_lt_of_lt_pow hne (by scalar_tac)
  refine ⟨hlt,?_⟩
  have hlo := Nat.pow_log_le_self 2 hne
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1<2) exponent.val
  rw [pow_succ] at hhi
  have hp : 0<2^(Nat.log 2 exponent.val) := pow_pos (by decide) _
  have hqlo : 1≤exponent.val/2^(Nat.log 2 exponent.val) := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hlo)
  have hqhi : exponent.val/2^(Nat.log 2 exponent.val)<2 := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_comm] using hhi)
  omega

abbrev Reverse32 := core.iter.adapters.rev.Rev (core.ops.range.Range U32)
abbrev reverse32Next := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepU32)

theorem reverse32_some_spec (iter : Reverse32) (hstart : iter.iter.start=0#u32)
    (hend : 0 < iter.iter.end.val) : reverse32Next iter
    ⦃ (opt : Option U32) (next : Reverse32) => ∃ bit : U32,
      opt=some bit ∧ next.iter.start=0#u32 ∧ next.iter.end=bit ∧
      bit.val+1=iter.iter.end.val ⦄ := by
  have hstep : 1 ≤ iter.iter.end.val := by omega
  simp [reverse32Next,core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepU32,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,core.cmp.impls.PartialOrdU32.lt,
    hstart,hend,hstep,WP.spec_ok,UScalar.ofNatCore_val_eq]

theorem reverse32_none_spec (iter : Reverse32) (hstart : iter.iter.start=0#u32)
    (hend : iter.iter.end.val=0) : reverse32Next iter
    ⦃ (opt : Option U32) (next : Reverse32) => opt=none ∧ next=iter ⦄ := by
  simp [reverse32Next,core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepU32,core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdU32.lt,hstart,hend,WP.spec_ok]

end UdonVerify.Native
