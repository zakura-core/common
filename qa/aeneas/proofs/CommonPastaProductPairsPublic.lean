import CommonProductPairsAPI
import CommonPastaProductPortablePublic

open Aeneas Std Result
namespace UdonVerify.ProductPairs
open UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Both production representation states on each side; any finite error-free iterator. -/
@[step]
theorem fp_sum_of_product_pairs_spec {S T C I : Type}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (into : core.iter.traits.collect.IntoIterator C (Element Native.Base S × Element Native.Base T) I)
    (source : C) (iter : I) (entries : List (Element Native.Base S × Element Native.Base T))
    (hinto : into.into_iter source = ok iter) (trace : FiniteTrace into.iteratorInst iter entries)
    (valid : ∀ pair ∈ entries,
      val4 pair.1.limbs < Native.productRepresentationBound Native.fpPrime leftRep ∧
      val4 pair.2.limbs < Native.productRepresentationBound Native.fpPrime rightRep) :
    sumOfPairs (portableDict Native.fpNativeInst) (productionState left) (productionState right) into source
      ⦃ out => val4 out.limbs < 2 * Native.fpPrime ∧
        Native.decode Native.fpPrime Native.fpRadixInverse out.limbs =
          decodedPairs Native.fpPrime Native.fpRadixInverse entries ⦄ := by
  have hvalid : ValidEntries (val4 Native.fpNativeParameters.modulus) leftRep.reduced rightRep.reduced entries := by
    intro pair hm
    have h := valid pair hm
    constructor
    · cases hr : leftRep.reduced <;>
        simpa [stateWeight, Native.productRepresentationBound, hr, Native.fp_native_prime_eq] using h.1
    · cases hr : rightRep.reduced <;>
        simpa [stateWeight, Native.productRepresentationBound, hr, Native.fp_native_prime_eq] using h.2
  simpa only [Native.fp_native_prime_eq] using
    pair_method_value_spec Native.fpNativeInst Native.fpNativeParameters Native.fpWideFieldParameters
      (productionState left) (productionState right) leftRep.reduced rightRep.reduced
      leftRep.reduced_ok rightRep.reduced_ok into source iter entries hinto trace hvalid
      Native.fpRadixInverse Native.fp_radix_inverse

/-- Both production representation states on each side; any finite error-free iterator. -/
@[step]
theorem fq_sum_of_product_pairs_spec {S T C I : Type}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (into : core.iter.traits.collect.IntoIterator C (Element Native.Scalar S × Element Native.Scalar T) I)
    (source : C) (iter : I) (entries : List (Element Native.Scalar S × Element Native.Scalar T))
    (hinto : into.into_iter source = ok iter) (trace : FiniteTrace into.iteratorInst iter entries)
    (valid : ∀ pair ∈ entries,
      val4 pair.1.limbs < Native.productRepresentationBound Native.fqPrime leftRep ∧
      val4 pair.2.limbs < Native.productRepresentationBound Native.fqPrime rightRep) :
    sumOfPairs (portableDict Native.fqNativeInst) (productionState left) (productionState right) into source
      ⦃ out => val4 out.limbs < 2 * Native.fqPrime ∧
        Native.decode Native.fqPrime Native.fqRadixInverse out.limbs =
          decodedPairs Native.fqPrime Native.fqRadixInverse entries ⦄ := by
  have hvalid : ValidEntries (val4 Native.fqNativeParameters.modulus) leftRep.reduced rightRep.reduced entries := by
    intro pair hm
    have h := valid pair hm
    constructor
    · cases hr : leftRep.reduced <;>
        simpa [stateWeight, Native.productRepresentationBound, hr, Native.fq_native_prime_eq] using h.1
    · cases hr : rightRep.reduced <;>
        simpa [stateWeight, Native.productRepresentationBound, hr, Native.fq_native_prime_eq] using h.2
  simpa only [Native.fq_native_prime_eq] using
    pair_method_value_spec Native.fqNativeInst Native.fqNativeParameters Native.fqWideFieldParameters
      (productionState left) (productionState right) leftRep.reduced rightRep.reduced
      leftRep.reduced_ok rightRep.reduced_ok into source iter entries hinto trace hvalid
      Native.fqRadixInverse Native.fq_radix_inverse

#print axioms fp_sum_of_product_pairs_spec
#print axioms fq_sum_of_product_pairs_spec
end UdonVerify.ProductPairs
