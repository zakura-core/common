import CommonProductPortableLanes
import NativeByteDecode

open Aeneas Std Result
namespace UdonVerify.ProductPortable
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem slice_count_bound {α : Type} (slice : Aeneas.Std.Slice α) : slice.length < B := by
  have h := slice.property
  rcases Usize.bounds_eq with hmax | hmax <;> rw [hmax] at h <;>
    norm_num [U32.max,U32.numBits,U64.max,U64.numBits,B] at h ⊢ <;> omega

@[step]
theorem portable_new_spec (M : Type) :
    CommonProductsPortable.field.pasta.products.ProductSum.new M ⦃ out => sumInteger out = 0 ⦄ := by
  unfold CommonProductsPortable.field.pasta.products.ProductSum.new
  simp [WP.spec_ok,sumInteger,sumToNative,Native.sumInteger,Native.accumulatorValue,val8]

@[step]
theorem initial_lanes_spec (M S T : Type) :
    core.array.from_fn 4#usize
      (CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum M S T)
      () ⦃ out => lanesInteger out = 0 ⦄ := by
  rw [Native.array_from_fn_four_eq]
  simp [CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum,
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice.closure.Insts.CoreOpsFunctionFnMutTupleUsizeProductSum.call_mut,
    CommonProductsPortable.field.pasta.products.ProductSum.new, WP.spec_ok,lanesInteger,
    sumInteger,sumToNative,Native.sumInteger,Native.accumulatorValue,val8]

#print axioms slice_count_bound
#print axioms portable_new_spec
#print axioms initial_lanes_spec
end UdonVerify.ProductPortable
