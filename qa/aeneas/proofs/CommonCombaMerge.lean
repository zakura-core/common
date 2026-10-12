import CommonCombaAdd
open Aeneas Std Result
open UdonVerify.Native
namespace UdonVerify.CommonComba
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def batchMergeColumn (result column : BatchColumn) : Result BatchColumn := do
  let left0 ← result.index_usize 0#usize
  let right0 ← column.index_usize 0#usize
  let pair0 ← NativeField.zakura_udon.field.pasta.word.adc left0 right0 0#u64
  let left1 ← result.index_usize 1#usize
  let right1 ← column.index_usize 1#usize
  let pair1 ← NativeField.zakura_udon.field.pasta.word.adc left1 right1 pair0.2
  let left2 ← result.index_usize 2#usize
  let right2 ← column.index_usize 2#usize
  let pair2 ← NativeField.zakura_udon.field.pasta.word.adc left2 right2 pair1.2
  massert (pair2.2 = 0#u64)
  ok (Aeneas.Std.Array.make 3#usize [pair0.1, pair1.1, pair2.1])

@[step]
theorem batch_merge_column_spec (result column : BatchColumn)
    (hbound : batchColumnInteger result + batchColumnInteger column < B ^ 3) :
    batchMergeColumn result column ⦃ out =>
      batchColumnInteger out = batchColumnInteger result + batchColumnInteger column ⦄ := by
  unfold batchMergeColumn
  step +scalarTac -grind as ⟨left0, hleft0⟩
  step +scalarTac -grind as ⟨right0, hright0⟩
  obtain ⟨digit0, carry0, hresult0, hsum0⟩ := product_adc_result left0 right0 0#u64
  rw [hresult0]
  simp only [bind_ok]
  step +scalarTac -grind as ⟨left1, hleft1⟩
  step +scalarTac -grind as ⟨right1, hright1⟩
  obtain ⟨digit1, carry1, hresult1, hsum1⟩ := product_adc_result left1 right1 carry0
  rw [hresult1]
  simp only [bind_ok]
  step +scalarTac -grind as ⟨left2, hleft2⟩
  step +scalarTac -grind as ⟨right2, hright2⟩
  obtain ⟨digit2, carry2, hresult2, hsum2⟩ := product_adc_result left2 right2 carry1
  rw [hresult2]
  simp only [bind_ok]
  have hvalue : batchColumnInteger (Aeneas.Std.Array.make 3#usize [digit0, digit1, digit2]) +
      B ^ 3 * carry2.val = batchColumnInteger result + batchColumnInteger column := by
    simp_all [batchColumnInteger, Array.make]
    norm_num [B] at *
    omega
  have hzero : carry2.val = 0 := by
    norm_num [B] at hvalue hbound
    omega
  have hcarryEq : carry2 = 0#u64 := UScalar.eq_of_val_eq (by simpa using hzero)
  subst carry2
  simp only [massert, ↓reduceIte, bind_ok, WP.spec_ok]
  simpa only [show (0#u64).val = 0 from by decide, mul_zero, add_zero] using hvalue

theorem adc_bridge (lhs rhs carry : U64) :
    CommonComba.field.pasta.word.adc lhs rhs carry=
      NativeField.zakura_udon.field.pasta.word.adc lhs rhs carry := by rfl

theorem merge_loop_unfold (iter : core.array.iter.IntoIter BatchColumn 3#usize) (result : BatchColumn) :
    CommonComba.field.pasta.products.merge_columns_loop iter result = (do
      let flow ← CommonComba.field.pasta.products.merge_columns_loop.body iter result
      match flow with
      | .done out => ok out
      | .cont (next,updated) => CommonComba.field.pasta.products.merge_columns_loop next updated) := by
  unfold CommonComba.field.pasta.products.merge_columns_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont state => rcases state with ⟨next,updated⟩;rfl

theorem merge_loop_body_bridge (iter : core.array.iter.IntoIter BatchColumn 3#usize) (result : BatchColumn) :
    CommonComba.field.pasta.products.merge_columns_loop.body iter result = (do
      let (item,next) ← core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter
      match item with
      | none => ok (ControlFlow.done result)
      | some column => do
        let updated ← batchMergeColumn result column
        ok (ControlFlow.cont (next,updated))) := by
  unfold CommonComba.field.pasta.products.merge_columns_loop.body batchMergeColumn
  simp only [adc_bridge,Std.bind_assoc,Std.uncurry,bind_ok]
  rfl

#print axioms batch_merge_column_spec
#print axioms adc_bridge
#print axioms merge_loop_body_bridge
end UdonVerify.CommonComba
