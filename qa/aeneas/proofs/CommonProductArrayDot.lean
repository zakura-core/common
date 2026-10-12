import CommonProductPairsPortableBridges
import CommonPastaProductPortablePublic

open Aeneas Std Result
namespace UdonVerify.ProductWrappers
open UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem array_slice_bridge {M S T : Type} {N : Usize} (inst : Modulus M) (left : State S) (right : State T)
    (lhs : Array (Element M S) N) (rhs : Array (Element M T) N) :
    CommonProductPairs.field.pasta.products.PastaField.sum_of_products inst left right lhs rhs =
      CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice inst left right
        (Array.to_slice lhs) (Array.to_slice rhs) := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_products
  simp only [lift, bind_ok]
  rw [ProductPairs.PortableBridge.field.pasta.products.PastaField.sum_of_products_slice]

theorem dot_slice_bridge {M S T : Type} (inst : Modulus M) (left : State S) (right : State T)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) :
    CommonProductPairs.field.pasta.products.dot inst left right lhs rhs =
      CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice inst left right lhs rhs := by
  unfold CommonProductPairs.field.pasta.products.dot
  rw [ProductPairs.PortableBridge.field.pasta.products.PastaField.sum_of_products_slice]

theorem dot_lengths_mismatch {M S T : Type} (inst : Modulus M) (left : State S) (right : State T)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length ≠ rhs.length) :
    CommonProductPairs.field.pasta.products.dot inst left right lhs rhs = fail Error.panic := by
  rw [dot_slice_bridge]
  exact slice_lengths_mismatch inst left right lhs rhs hlen

/-- Both fields and all four loose/reduced state pairs use the proved slice implementation. -/
@[step]
theorem fp_array_sum_spec {S T : Type} {N : Usize}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (lhs : Array (Element Native.Base S) N) (rhs : Array (Element Native.Base T) N)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < Native.productRepresentationBound Native.fpPrime leftRep)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < Native.productRepresentationBound Native.fpPrime rightRep) :
    CommonProductPairs.field.pasta.products.PastaField.sum_of_products
      (portableDict Native.fpNativeInst) (productionState left) (productionState right) lhs rhs
      ⦃ out => val4 out.limbs < 2 * Native.fpPrime ∧
        Native.decode Native.fpPrime Native.fpRadixInverse out.limbs =
          decodedSum Native.fpPrime Native.fpRadixInverse (Array.to_slice lhs) (Array.to_slice rhs) ⦄ := by
  rw [array_slice_bridge]
  apply fp_sum_of_products_portable_spec left right leftRep rightRep (Array.to_slice lhs) (Array.to_slice rhs)
    (by simp [Array.to_slice,Aeneas.Std.Slice.length,lhs.property,rhs.property])
    (by simpa [Array.to_slice] using ha) (by simpa [Array.to_slice] using hb)

/-- Both fields and all four loose/reduced state pairs use the proved slice implementation. -/
@[step]
theorem fp_dot_spec {S T : Type}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (lhs : Aeneas.Std.Slice (Element Native.Base S)) (rhs : Aeneas.Std.Slice (Element Native.Base T))
    (hlen : lhs.length = rhs.length)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < Native.productRepresentationBound Native.fpPrime leftRep)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < Native.productRepresentationBound Native.fpPrime rightRep) :
    CommonProductPairs.field.pasta.products.dot
      (portableDict Native.fpNativeInst) (productionState left) (productionState right) lhs rhs
      ⦃ out => val4 out.limbs < 2 * Native.fpPrime ∧
        Native.decode Native.fpPrime Native.fpRadixInverse out.limbs =
          decodedSum Native.fpPrime Native.fpRadixInverse lhs rhs ⦄ := by
  rw [dot_slice_bridge]
  apply fp_sum_of_products_portable_spec left right leftRep rightRep lhs rhs
    hlen ha hb

/-- Both fields and all four loose/reduced state pairs use the proved slice implementation. -/
@[step]
theorem fq_array_sum_spec {S T : Type} {N : Usize}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (lhs : Array (Element Native.Scalar S) N) (rhs : Array (Element Native.Scalar T) N)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < Native.productRepresentationBound Native.fqPrime leftRep)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < Native.productRepresentationBound Native.fqPrime rightRep) :
    CommonProductPairs.field.pasta.products.PastaField.sum_of_products
      (portableDict Native.fqNativeInst) (productionState left) (productionState right) lhs rhs
      ⦃ out => val4 out.limbs < 2 * Native.fqPrime ∧
        Native.decode Native.fqPrime Native.fqRadixInverse out.limbs =
          decodedSum Native.fqPrime Native.fqRadixInverse (Array.to_slice lhs) (Array.to_slice rhs) ⦄ := by
  rw [array_slice_bridge]
  apply fq_sum_of_products_portable_spec left right leftRep rightRep (Array.to_slice lhs) (Array.to_slice rhs)
    (by simp [Array.to_slice,Aeneas.Std.Slice.length,lhs.property,rhs.property])
    (by simpa [Array.to_slice] using ha) (by simpa [Array.to_slice] using hb)

/-- Both fields and all four loose/reduced state pairs use the proved slice implementation. -/
@[step]
theorem fq_dot_spec {S T : Type}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (lhs : Aeneas.Std.Slice (Element Native.Scalar S)) (rhs : Aeneas.Std.Slice (Element Native.Scalar T))
    (hlen : lhs.length = rhs.length)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < Native.productRepresentationBound Native.fqPrime leftRep)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < Native.productRepresentationBound Native.fqPrime rightRep) :
    CommonProductPairs.field.pasta.products.dot
      (portableDict Native.fqNativeInst) (productionState left) (productionState right) lhs rhs
      ⦃ out => val4 out.limbs < 2 * Native.fqPrime ∧
        Native.decode Native.fqPrime Native.fqRadixInverse out.limbs =
          decodedSum Native.fqPrime Native.fqRadixInverse lhs rhs ⦄ := by
  rw [dot_slice_bridge]
  apply fq_sum_of_products_portable_spec left right leftRep rightRep lhs rhs
    hlen ha hb

#print axioms array_slice_bridge
#print axioms dot_slice_bridge
#print axioms dot_lengths_mismatch
#print axioms fp_array_sum_spec
#print axioms fp_dot_spec
#print axioms fq_array_sum_spec
#print axioms fq_dot_spec
end UdonVerify.ProductWrappers
