import CommonProductSerialAPI
import NativeWideParameters

open Aeneas Std Result
namespace UdonVerify.ProductSerial
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Retain every flag and method in the production representation dictionary. -/
def productionState {S : Type} (state : Native.ProductState S) : State S where
  sealedSealedInst := ⟨state.sealedSealedInst.REDUCED⟩
  coremarkerCopyInst := state.coremarkerCopyInst
  corecmpEqInst := state.corecmpEqInst

theorem production_state_flag {S : Type} (state : Native.ProductState S) :
    (productionState state).sealedSealedInst.REDUCED = state.sealedSealedInst.REDUCED := by rfl

/-- The serial sum contract accepts both production input states, even without
    requiring a bound stronger than the stored four-word representation. -/
@[step]
theorem fp_sum_of_products_serial_spec {S T : Type}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (lhs : Aeneas.Std.Slice (Element Native.Base S)) (rhs : Aeneas.Std.Slice (Element Native.Base T))
    (hlen : lhs.length = rhs.length) (hmin : 4 ≤ lhs.length) (hmax : lhs.length < 64) :
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice
      (serialDict Native.fpNativeInst) (productionState left) (productionState right) lhs rhs ⦃ out =>
        val4 out.limbs < 2 * Native.fpPrime ∧
        Native.decode Native.fpPrime Native.fpRadixInverse out.limbs =
          decodedSum Native.fpPrime Native.fpRadixInverse lhs rhs ⦄ := by
  simpa only [Native.fp_native_prime_eq] using
    serial_slice_value_spec Native.fpNativeInst Native.fpNativeParameters Native.fpWideFieldParameters
      (productionState left) (productionState right) lhs rhs hlen hmin hmax
      Native.fpRadixInverse Native.fp_radix_inverse

/-- The serial sum contract accepts both production input states, even without
    requiring a bound stronger than the stored four-word representation. -/
@[step]
theorem fq_sum_of_products_serial_spec {S T : Type}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (lhs : Aeneas.Std.Slice (Element Native.Scalar S)) (rhs : Aeneas.Std.Slice (Element Native.Scalar T))
    (hlen : lhs.length = rhs.length) (hmin : 4 ≤ lhs.length) (hmax : lhs.length < 64) :
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice
      (serialDict Native.fqNativeInst) (productionState left) (productionState right) lhs rhs ⦃ out =>
        val4 out.limbs < 2 * Native.fqPrime ∧
        Native.decode Native.fqPrime Native.fqRadixInverse out.limbs =
          decodedSum Native.fqPrime Native.fqRadixInverse lhs rhs ⦄ := by
  simpa only [Native.fq_native_prime_eq] using
    serial_slice_value_spec Native.fqNativeInst Native.fqNativeParameters Native.fqWideFieldParameters
      (productionState left) (productionState right) lhs rhs hlen hmin hmax
      Native.fqRadixInverse Native.fq_radix_inverse

#print axioms production_state_flag
#print axioms fp_sum_of_products_serial_spec
#print axioms fq_sum_of_products_serial_spec
end UdonVerify.ProductSerial
