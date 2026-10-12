import CommonProductDotIterAPI

open Aeneas Std Result
namespace UdonVerify.ProductWrappers
open UdonVerify.ProductPairs UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Correct finite iteration, length reporting and zip construction; all four state pairs. -/
@[step]
theorem fp_dot_iter_spec {S T A B I J : Type}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (intoL : core.iter.traits.collect.IntoIterator A (Element Native.Base S) I)
    (intoR : core.iter.traits.collect.IntoIterator B (Element Native.Base T) J)
    (opsL : ExactOps I (Element Native.Base S)) (opsR : ExactOps J (Element Native.Base T))
    (lhs : A) (rhs : B) (il : I) (ir : J) (nl nr : Usize)
    (xs : List (Element Native.Base S)) (ys : List (Element Native.Base T))
    (hintoL : intoL.into_iter lhs = ok il) (hintoR : intoR.into_iter rhs = ok ir)
    (hlenL : opsL.len il = ok nl) (hlenR : opsR.len ir = ok nr)
    (hsizeL : nl.val = xs.length) (hsizeR : nr.val = ys.length) (hlen : xs.length = ys.length)
    (hzip : opsL.zip (core.iter.traits.collect.IntoIterator.Blanket opsR.iteratorInst) il ir =
      ok (⟨il,ir⟩ : core.iter.adapters.zip.Zip I J))
    (tl : FiniteTrace opsL.iteratorInst il xs) (tr : FiniteTrace opsR.iteratorInst ir ys)
    (ha : ∀ a ∈ xs, val4 a.limbs < Native.productRepresentationBound Native.fpPrime leftRep)
    (hb : ∀ b ∈ ys, val4 b.limbs < Native.productRepresentationBound Native.fpPrime rightRep) :
    dotIter (portableDict Native.fpNativeInst) (productionState left) (productionState right)
      intoL intoR opsL opsR lhs rhs ⦃ out => val4 out.limbs < 2 * Native.fpPrime ∧
        Native.decode Native.fpPrime Native.fpRadixInverse out.limbs =
          rawSum (fun a => Native.decode Native.fpPrime Native.fpRadixInverse a.limbs)
            (fun b => Native.decode Native.fpPrime Native.fpRadixInverse b.limbs) xs ys % Native.fpPrime ⦄ := by
  have ha' : ∀ a ∈ xs, val4 a.limbs < stateWeight leftRep.reduced * val4 Native.fpNativeParameters.modulus := by
    intro a hm
    have h := ha a hm
    cases hr : leftRep.reduced <;>
      simpa [stateWeight, Native.productRepresentationBound, hr, Native.fp_native_prime_eq] using h
  have hb' : ∀ b ∈ ys, val4 b.limbs < stateWeight rightRep.reduced * val4 Native.fpNativeParameters.modulus := by
    intro b hm
    have h := hb b hm
    cases hr : rightRep.reduced <;>
      simpa [stateWeight, Native.productRepresentationBound, hr, Native.fp_native_prime_eq] using h
  simpa only [Native.fp_native_prime_eq] using
    dot_iter_value_spec Native.fpNativeInst Native.fpNativeParameters Native.fpWideFieldParameters
      (productionState left) (productionState right) leftRep.reduced rightRep.reduced
      leftRep.reduced_ok rightRep.reduced_ok intoL intoR opsL opsR lhs rhs il ir nl nr xs ys
      hintoL hintoR hlenL hlenR hsizeL hsizeR hlen hzip tl tr ha' hb'
      Native.fpRadixInverse Native.fp_radix_inverse

/-- Correct finite iteration, length reporting and zip construction; all four state pairs. -/
@[step]
theorem fq_dot_iter_spec {S T A B I J : Type}
    (left : Native.ProductState S) (right : Native.ProductState T)
    (leftRep : Native.ProductRepresentation left) (rightRep : Native.ProductRepresentation right)
    (intoL : core.iter.traits.collect.IntoIterator A (Element Native.Scalar S) I)
    (intoR : core.iter.traits.collect.IntoIterator B (Element Native.Scalar T) J)
    (opsL : ExactOps I (Element Native.Scalar S)) (opsR : ExactOps J (Element Native.Scalar T))
    (lhs : A) (rhs : B) (il : I) (ir : J) (nl nr : Usize)
    (xs : List (Element Native.Scalar S)) (ys : List (Element Native.Scalar T))
    (hintoL : intoL.into_iter lhs = ok il) (hintoR : intoR.into_iter rhs = ok ir)
    (hlenL : opsL.len il = ok nl) (hlenR : opsR.len ir = ok nr)
    (hsizeL : nl.val = xs.length) (hsizeR : nr.val = ys.length) (hlen : xs.length = ys.length)
    (hzip : opsL.zip (core.iter.traits.collect.IntoIterator.Blanket opsR.iteratorInst) il ir =
      ok (⟨il,ir⟩ : core.iter.adapters.zip.Zip I J))
    (tl : FiniteTrace opsL.iteratorInst il xs) (tr : FiniteTrace opsR.iteratorInst ir ys)
    (ha : ∀ a ∈ xs, val4 a.limbs < Native.productRepresentationBound Native.fqPrime leftRep)
    (hb : ∀ b ∈ ys, val4 b.limbs < Native.productRepresentationBound Native.fqPrime rightRep) :
    dotIter (portableDict Native.fqNativeInst) (productionState left) (productionState right)
      intoL intoR opsL opsR lhs rhs ⦃ out => val4 out.limbs < 2 * Native.fqPrime ∧
        Native.decode Native.fqPrime Native.fqRadixInverse out.limbs =
          rawSum (fun a => Native.decode Native.fqPrime Native.fqRadixInverse a.limbs)
            (fun b => Native.decode Native.fqPrime Native.fqRadixInverse b.limbs) xs ys % Native.fqPrime ⦄ := by
  have ha' : ∀ a ∈ xs, val4 a.limbs < stateWeight leftRep.reduced * val4 Native.fqNativeParameters.modulus := by
    intro a hm
    have h := ha a hm
    cases hr : leftRep.reduced <;>
      simpa [stateWeight, Native.productRepresentationBound, hr, Native.fq_native_prime_eq] using h
  have hb' : ∀ b ∈ ys, val4 b.limbs < stateWeight rightRep.reduced * val4 Native.fqNativeParameters.modulus := by
    intro b hm
    have h := hb b hm
    cases hr : rightRep.reduced <;>
      simpa [stateWeight, Native.productRepresentationBound, hr, Native.fq_native_prime_eq] using h
  simpa only [Native.fq_native_prime_eq] using
    dot_iter_value_spec Native.fqNativeInst Native.fqNativeParameters Native.fqWideFieldParameters
      (productionState left) (productionState right) leftRep.reduced rightRep.reduced
      leftRep.reduced_ok rightRep.reduced_ok intoL intoR opsL opsR lhs rhs il ir nl nr xs ys
      hintoL hintoR hlenL hlenR hsizeL hsizeR hlen hzip tl tr ha' hb'
      Native.fqRadixInverse Native.fq_radix_inverse

#print axioms fp_dot_iter_spec
#print axioms fq_dot_iter_spec
end UdonVerify.ProductWrappers
