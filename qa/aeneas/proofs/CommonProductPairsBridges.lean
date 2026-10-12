import CommonProductPairsInner
import CommonPastaProductPortablePublic

open Aeneas Std Result
namespace UdonVerify.ProductPairs
open UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem pairs_slice_bridge {M S T : Type} (inst : Modulus M) (left : State S) (right : State T)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice inst left right lhs rhs =
      CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice inst left right lhs rhs := by rw [PortableBridge.field.pasta.products.PastaField.sum_of_products_slice]

theorem pairs_new_bridge (M : Type) :
    CommonProductPairs.field.pasta.products.ProductSum.new M =
      CommonProductsPortable.field.pasta.products.ProductSum.new M := by rw [PortableBridge.field.pasta.products.ProductSum.new]

theorem pairs_finish_bridge {M : Type} (inst : Modulus M) (sum : Sum M) :
    CommonProductPairs.field.pasta.products.ProductSum.finish inst sum =
      CommonProductsPortable.field.pasta.products.ProductSum.finish inst sum := by rw [PortableBridge.field.pasta.products.ProductSum.finish]

theorem pairs_multiply_bridge {M S T : Type} (inst : Modulus M) (lhs : Element M S) (rhs : Element M T) :
    CommonProductPairs.field.pasta.PastaField.mul inst lhs rhs =
      CommonProductsPortable.field.pasta.PastaField.mul inst lhs rhs := by rw [PortableBridge.field.pasta.PastaField.mul]

theorem pairs_bounded_bridge {M S T : Type} (inst : Modulus M) (sum : Sum M)
    (lhs : Element M S) (rhs : Element M T) :
    CommonProductPairs.field.pasta.products.ProductSum.add_product_inner true inst sum lhs rhs =
      CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner true inst sum lhs rhs := by rw [PortableBridge.field.pasta.products.ProductSum.add_product_inner]

@[step]
theorem pairs_add_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (sum : Sum M) (lhs : Element M S) (rhs : Element M T) :
    CommonProductPairs.field.pasta.products.ProductSum.add_product (portableDict inst) sum lhs rhs
      ⦃ out => Nat.ModEq (val4 params.modulus) (sumInteger out)
        (sumInteger sum + val4 lhs.limbs * val4 rhs.limbs) ⦄ := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.add_product
  apply WP.spec_mono (pairs_inner_spec false inst params constants sum lhs rhs (by simp))
  intro out hout
  exact hout.1

/-- Reconstruct the original single production dictionary at the public boundary. -/
def sumOfPairs {M S T C I : Type} (inst : Modulus M) (left : State S) (right : State T)
    (into : core.iter.traits.collect.IntoIterator C (Element M S × Element M T) I) (source : C) :
    Result (Element M Loose) :=
  CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs inst left right into into.iteratorInst source

theorem production_iterator_argument {M S T C I : Type} (inst : Modulus M) (left : State S) (right : State T)
    (into : core.iter.traits.collect.IntoIterator C (Element M S × Element M T) I) (source : C) :
    sumOfPairs inst left right into source =
      CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs inst left right into into.iteratorInst source := by rfl

#print axioms pairs_slice_bridge
#print axioms pairs_new_bridge
#print axioms pairs_finish_bridge
#print axioms pairs_multiply_bridge
#print axioms pairs_bounded_bridge
#print axioms pairs_add_spec
#print axioms production_iterator_argument
end UdonVerify.ProductPairs
