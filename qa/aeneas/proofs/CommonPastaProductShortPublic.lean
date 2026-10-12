import CommonProductShortValue
import NativeCanonical

open Aeneas Std Result
namespace UdonVerify.ProductShort
open UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Copy the production representation dictionary, retaining every flag and method. -/
def productionState {S : Type} (state : Native.ProductState S) : State S where
  sealedSealedInst := ⟨state.sealedSealedInst.REDUCED⟩
  coremarkerCopyInst := state.coremarkerCopyInst
  corecmpEqInst := state.corecmpEqInst

theorem production_state_flag {S : Type} (state : Native.ProductState S) :
    (productionState state).sealedSealedInst.REDUCED = state.sealedSealedInst.REDUCED := by rfl

/-- All four loose/reduced input pairs are covered by their production state dictionaries. -/
@[step]
theorem fp_sum_of_products_short_spec {S T : Type} (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (lhs : Aeneas.Std.Slice (Element Native.Base S)) (rhs : Aeneas.Std.Slice (Element Native.Base T))
    (hlen : lhs.length = rhs.length) (hshort : lhs.length ≤ 3)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < Native.productRepresentationBound Native.fpPrime leftRep)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < Native.productRepresentationBound Native.fpPrime rightRep) :
    CommonProductShort.field.pasta.products.PastaField.sum_of_products_slice
      (shortDict Native.fpNativeInst) (productionState left) (productionState right) lhs rhs ⦃ out =>
        val4 out.limbs < 2 * Native.fpPrime ∧
        Native.decode Native.fpPrime Native.fpRadixInverse out.limbs =
          decodedSum Native.fpPrime Native.fpRadixInverse lhs rhs ⦄ := by
  have ha' : ∀ a ∈ lhs.val, val4 a.limbs < stateWeight leftRep.reduced * val4 Native.fpNativeParameters.modulus := by
    intro a hm
    have h := ha a hm
    cases hr : leftRep.reduced <;>
      simpa [stateWeight, Native.productRepresentationBound, hr, Native.fp_native_prime_eq] using h
  have hb' : ∀ b ∈ rhs.val, val4 b.limbs < stateWeight rightRep.reduced * val4 Native.fpNativeParameters.modulus := by
    intro b hm
    have h := hb b hm
    cases hr : rightRep.reduced <;>
      simpa [stateWeight, Native.productRepresentationBound, hr, Native.fp_native_prime_eq] using h
  simpa only [Native.fp_native_prime_eq] using
    slice_short_value_spec Native.fpNativeInst Native.fpNativeParameters
      (productionState left) (productionState right) leftRep.reduced rightRep.reduced
      leftRep.reduced_ok rightRep.reduced_ok lhs rhs hlen hshort ha' hb'
      Native.fpRadixInverse Native.fp_radix_inverse

/-- All four loose/reduced input pairs are covered by their production state dictionaries. -/
@[step]
theorem fq_sum_of_products_short_spec {S T : Type} (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (lhs : Aeneas.Std.Slice (Element Native.Scalar S)) (rhs : Aeneas.Std.Slice (Element Native.Scalar T))
    (hlen : lhs.length = rhs.length) (hshort : lhs.length ≤ 3)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < Native.productRepresentationBound Native.fqPrime leftRep)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < Native.productRepresentationBound Native.fqPrime rightRep) :
    CommonProductShort.field.pasta.products.PastaField.sum_of_products_slice
      (shortDict Native.fqNativeInst) (productionState left) (productionState right) lhs rhs ⦃ out =>
        val4 out.limbs < 2 * Native.fqPrime ∧
        Native.decode Native.fqPrime Native.fqRadixInverse out.limbs =
          decodedSum Native.fqPrime Native.fqRadixInverse lhs rhs ⦄ := by
  have ha' : ∀ a ∈ lhs.val, val4 a.limbs < stateWeight leftRep.reduced * val4 Native.fqNativeParameters.modulus := by
    intro a hm
    have h := ha a hm
    cases hr : leftRep.reduced <;>
      simpa [stateWeight, Native.productRepresentationBound, hr, Native.fq_native_prime_eq] using h
  have hb' : ∀ b ∈ rhs.val, val4 b.limbs < stateWeight rightRep.reduced * val4 Native.fqNativeParameters.modulus := by
    intro b hm
    have h := hb b hm
    cases hr : rightRep.reduced <;>
      simpa [stateWeight, Native.productRepresentationBound, hr, Native.fq_native_prime_eq] using h
  simpa only [Native.fq_native_prime_eq] using
    slice_short_value_spec Native.fqNativeInst Native.fqNativeParameters
      (productionState left) (productionState right) leftRep.reduced rightRep.reduced
      leftRep.reduced_ok rightRep.reduced_ok lhs rhs hlen hshort ha' hb'
      Native.fqRadixInverse Native.fq_radix_inverse

#print axioms production_state_flag
#print axioms fp_sum_of_products_short_spec
#print axioms fq_sum_of_products_short_spec
end UdonVerify.ProductShort
