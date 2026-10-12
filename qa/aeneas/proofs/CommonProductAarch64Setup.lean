import CommonProductAarch64Dictionaries

open Aeneas Std Result
namespace UdonVerify.ProductAarch64
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem slice_count_bound {α : Type} (slice : Aeneas.Std.Slice α) : slice.length < B := by
  have h := slice.property
  rcases Usize.bounds_eq with hmax | hmax <;> rw [hmax] at h <;>
    norm_num [U32.max,U32.numBits,U64.max,U64.numBits,B] at h ⊢ <;> omega

@[step]
theorem aarch64_new_spec (M : Type) :
    CommonProductsAarch64.field.pasta.products.ProductSum.new M ⦃ out => sumInteger out = 0 ⦄ := by
  unfold CommonProductsAarch64.field.pasta.products.ProductSum.new
  simp [WP.spec_ok,sumInteger,sumToNative,Native.sumInteger,Native.accumulatorValue,val8]

#print axioms slice_count_bound
#print axioms aarch64_new_spec
end UdonVerify.ProductAarch64
