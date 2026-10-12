import CommonCombaMerge

open Aeneas Std Result
open UdonVerify.Native
namespace UdonVerify.CommonComba
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev BatchColumns := Aeneas.Std.Array BatchColumn 4#usize

def batchColumnsInteger (columns : BatchColumns) : Nat :=
  batchColumnInteger columns[0]! + batchColumnInteger columns[1]! +
    batchColumnInteger columns[2]! + batchColumnInteger columns[3]!

def mergeIterator (a b c : BatchColumn) (index : Nat) :
    core.array.iter.IntoIter BatchColumn 3#usize :=
  ⟨Slice.from [a,b,c] (by scalar_tac),index⟩

theorem merge_next_zero (a b c : BatchColumn) :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
      (mergeIterator a b c 0) = ok (some a,mergeIterator a b c 1) := by
  simp [mergeIterator,core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorSliceIter.next]

theorem merge_next_one (a b c : BatchColumn) :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
      (mergeIterator a b c 1) = ok (some b,mergeIterator a b c 2) := by
  simp [mergeIterator,core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorSliceIter.next]

theorem merge_next_two (a b c : BatchColumn) :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
      (mergeIterator a b c 2) = ok (some c,mergeIterator a b c 3) := by
  simp [mergeIterator,core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorSliceIter.next]

theorem merge_next_end (a b c : BatchColumn) :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
      (mergeIterator a b c 3) = ok (none,mergeIterator a b c 3) := by
  simp [mergeIterator,core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorSliceIter.next]

@[step]
theorem merge_three_spec (initial a b c : BatchColumn)
    (hbound : batchColumnInteger initial + batchColumnInteger a +
      batchColumnInteger b + batchColumnInteger c < B ^ 3) :
    CommonComba.field.pasta.products.merge_columns_loop
      (mergeIterator a b c 0) initial ⦃ out =>
        batchColumnInteger out = batchColumnInteger initial + batchColumnInteger a +
          batchColumnInteger b + batchColumnInteger c ⦄ := by
  rw [merge_loop_unfold,merge_loop_body_bridge,merge_next_zero]
  simp only [bind_ok,Std.uncurry]
  step -grind with (batch_merge_column_spec initial a (by omega)) as ⟨sum1,hsum1⟩
  try simp only [bind_ok]
  rw [merge_loop_unfold,merge_loop_body_bridge,merge_next_one]
  simp only [bind_ok,Std.uncurry]
  step -grind with (batch_merge_column_spec sum1 b (by omega)) as ⟨sum2,hsum2⟩
  try simp only [bind_ok]
  rw [merge_loop_unfold,merge_loop_body_bridge,merge_next_two]
  simp only [bind_ok,Std.uncurry]
  step -grind with (batch_merge_column_spec sum2 c (by omega)) as ⟨sum3,hsum3⟩
  try simp only [bind_ok]
  rw [merge_loop_unfold,merge_loop_body_bridge,merge_next_end]
  simp only [bind_ok,Std.uncurry,WP.spec_ok]
  omega

@[step]
theorem batch_merge_columns_spec (columns : BatchColumns)
    (hbound : batchColumnsInteger columns < B ^ 3) :
    CommonComba.field.pasta.products.merge_columns columns ⦃ out =>
      batchColumnInteger out = batchColumnsInteger columns ⦄ := by
  unfold CommonComba.field.pasta.products.merge_columns
  step +scalarTac -grind as ⟨initial,hinitial⟩
  step +scalarTac -grind as ⟨a,ha⟩
  step +scalarTac -grind as ⟨b,hb⟩
  step +scalarTac -grind as ⟨c,hc⟩
  simp only [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    Array.make,bind_ok]
  change CommonComba.field.pasta.products.merge_columns_loop
    (mergeIterator a b c 0) initial ⦃ out =>
      batchColumnInteger out = batchColumnsInteger columns ⦄
  have htotal : batchColumnsInteger columns = batchColumnInteger initial +
      batchColumnInteger a + batchColumnInteger b + batchColumnInteger c := by
    simp_all [batchColumnsInteger]
  rw [htotal] at hbound ⊢
  exact merge_three_spec initial a b c hbound

theorem batch_columns_seed (column : BatchColumn) :
    batchColumnsInteger (Aeneas.Std.Array.make 4#usize [column,
      Aeneas.Std.Array.repeat 3#usize 0#u64,Aeneas.Std.Array.repeat 3#usize 0#u64,
      Aeneas.Std.Array.repeat 3#usize 0#u64]) = batchColumnInteger column := by
  simp [batchColumnsInteger,batchColumnInteger,Array.make,Array.repeat]

@[step]
theorem batch_start_columns_spec (accumulator carryLow carryHigh : U64) :
    CommonComba.field.pasta.products.start_columns accumulator carryLow carryHigh ⦃ out =>
      batchColumnsInteger out = accumulator.val + carryLow.val + B * carryHigh.val ∧
        batchColumnsInteger out < 2 * B ^ 2 ⦄ := by
  unfold CommonComba.field.pasta.products.start_columns
  step -grind with (batch_start_column_spec accumulator carryLow carryHigh) as ⟨column,hvalue,hbound⟩
  simp only [batch_columns_seed]
  exact ⟨hvalue,hbound⟩

#print axioms merge_three_spec
#print axioms batch_merge_columns_spec
#print axioms batch_start_columns_spec
end UdonVerify.CommonComba
