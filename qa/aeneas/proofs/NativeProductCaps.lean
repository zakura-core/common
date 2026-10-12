import NativeProductValue
import NativeCanonical

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

@[step]
theorem fp_sum_new_spec : NativeField.fp_sum_new
    ⦃ out => sumValue fpPrime fpRadixInverse out = 0 ⦄ := by
  unfold NativeField.fp_sum_new
  step -grind with (product_new_spec Base) as ⟨out, hout⟩
  simp [sumValue, hout]

#print axioms fp_sum_new_spec

@[step]
theorem fp_product_add_generic_spec {S T : Type} (sum : Sum Base)
    (lhs : Element Base S) (rhs : Element Base T) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_product fpNativeInst sum lhs rhs
      ⦃ out => sumValue fpPrime fpRadixInverse out =
        (sumValue fpPrime fpRadixInverse sum + decode fpPrime fpRadixInverse lhs.limbs *
          decode fpPrime fpRadixInverse rhs.limbs) % fpPrime ⦄ := by
  simpa only [fp_native_prime_eq] using
    product_add_product_value_spec fpNativeInst fpNativeParameters fpWideFieldParameters fpRadixInverse sum lhs rhs

#print axioms fp_product_add_generic_spec

@[step]
theorem fp_product_square_generic_spec {S : Type} (sum : Sum Base) (value : Element Base S) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_square fpNativeInst sum value
      ⦃ out => sumValue fpPrime fpRadixInverse out =
        (sumValue fpPrime fpRadixInverse sum + decode fpPrime fpRadixInverse value.limbs ^ 2) % fpPrime ⦄ := by
  simpa only [fp_native_prime_eq] using
    product_add_square_value_spec fpNativeInst fpNativeParameters fpWideFieldParameters fpRadixInverse sum value

#print axioms fp_product_square_generic_spec

@[step]
theorem fp_product_term_generic_spec {S : Type} (sum : Sum Base) (term : Element Base S) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_term fpNativeInst sum term
      ⦃ out => sumValue fpPrime fpRadixInverse out =
        (sumValue fpPrime fpRadixInverse sum + decode fpPrime fpRadixInverse term.limbs) % fpPrime ⦄ := by
  simpa only [fp_native_prime_eq] using
    product_add_term_value_spec fpNativeInst fpNativeParameters fpWideFieldParameters fpRadixInverse fp_radix_inverse sum term

#print axioms fp_product_term_generic_spec

@[step]
theorem fp_sum_add_product_spec (sum : Sum Base) (lhs rhs : Element Base Loose) :
    NativeField.fp_sum_add_product sum lhs rhs
      ⦃ out => sumValue fpPrime fpRadixInverse out =
        (sumValue fpPrime fpRadixInverse sum + decode fpPrime fpRadixInverse lhs.limbs *
          decode fpPrime fpRadixInverse rhs.limbs) % fpPrime ⦄ := by
  unfold NativeField.fp_sum_add_product
  exact fp_product_add_generic_spec sum lhs rhs

#print axioms fp_sum_add_product_spec

@[step]
theorem fp_sum_add_square_spec (sum : Sum Base) (value : Element Base Loose) :
    NativeField.fp_sum_add_square sum value
      ⦃ out => sumValue fpPrime fpRadixInverse out =
        (sumValue fpPrime fpRadixInverse sum + decode fpPrime fpRadixInverse value.limbs ^ 2) % fpPrime ⦄ := by
  unfold NativeField.fp_sum_add_square
  exact fp_product_square_generic_spec sum value

#print axioms fp_sum_add_square_spec

@[step]
theorem fp_sum_add_term_spec (sum : Sum Base) (term : Element Base Loose) :
    NativeField.fp_sum_add_term sum term
      ⦃ out => sumValue fpPrime fpRadixInverse out =
        (sumValue fpPrime fpRadixInverse sum + decode fpPrime fpRadixInverse term.limbs) % fpPrime ⦄ := by
  unfold NativeField.fp_sum_add_term
  exact fp_product_term_generic_spec sum term

#print axioms fp_sum_add_term_spec

@[step]
theorem fp_sum_merge_spec (sum other : Sum Base) :
    NativeField.fp_sum_merge sum other
      ⦃ out => sumValue fpPrime fpRadixInverse out =
        (sumValue fpPrime fpRadixInverse sum + sumValue fpPrime fpRadixInverse other) % fpPrime ⦄ := by
  unfold NativeField.fp_sum_merge
  simpa only [fp_native_prime_eq] using product_merge_value_spec fpNativeInst fpNativeParameters fpWideFieldParameters fpRadixInverse sum other

#print axioms fp_sum_merge_spec

@[step]
theorem fp_sum_finish_spec (sum : Sum Base) :
    NativeField.fp_sum_finish sum
      ⦃ out => val4 out.limbs < 2 * fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs = sumValue fpPrime fpRadixInverse sum ⦄ := by
  unfold NativeField.fp_sum_finish
  simpa only [fp_native_prime_eq] using
    product_finish_value_spec fpNativeInst fpNativeParameters fpWideFieldParameters fpRadixInverse fp_radix_inverse sum

#print axioms fp_sum_finish_spec

@[step]
theorem fq_sum_new_spec : NativeField.fq_sum_new
    ⦃ out => sumValue fqPrime fqRadixInverse out = 0 ⦄ := by
  unfold NativeField.fq_sum_new
  step -grind with (product_new_spec Scalar) as ⟨out, hout⟩
  simp [sumValue, hout]

#print axioms fq_sum_new_spec

@[step]
theorem fq_product_add_generic_spec {S T : Type} (sum : Sum Scalar)
    (lhs : Element Scalar S) (rhs : Element Scalar T) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_product fqNativeInst sum lhs rhs
      ⦃ out => sumValue fqPrime fqRadixInverse out =
        (sumValue fqPrime fqRadixInverse sum + decode fqPrime fqRadixInverse lhs.limbs *
          decode fqPrime fqRadixInverse rhs.limbs) % fqPrime ⦄ := by
  simpa only [fq_native_prime_eq] using
    product_add_product_value_spec fqNativeInst fqNativeParameters fqWideFieldParameters fqRadixInverse sum lhs rhs

#print axioms fq_product_add_generic_spec

@[step]
theorem fq_product_square_generic_spec {S : Type} (sum : Sum Scalar) (value : Element Scalar S) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_square fqNativeInst sum value
      ⦃ out => sumValue fqPrime fqRadixInverse out =
        (sumValue fqPrime fqRadixInverse sum + decode fqPrime fqRadixInverse value.limbs ^ 2) % fqPrime ⦄ := by
  simpa only [fq_native_prime_eq] using
    product_add_square_value_spec fqNativeInst fqNativeParameters fqWideFieldParameters fqRadixInverse sum value

#print axioms fq_product_square_generic_spec

@[step]
theorem fq_product_term_generic_spec {S : Type} (sum : Sum Scalar) (term : Element Scalar S) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_term fqNativeInst sum term
      ⦃ out => sumValue fqPrime fqRadixInverse out =
        (sumValue fqPrime fqRadixInverse sum + decode fqPrime fqRadixInverse term.limbs) % fqPrime ⦄ := by
  simpa only [fq_native_prime_eq] using
    product_add_term_value_spec fqNativeInst fqNativeParameters fqWideFieldParameters fqRadixInverse fq_radix_inverse sum term

#print axioms fq_product_term_generic_spec

@[step]
theorem fq_sum_add_product_spec (sum : Sum Scalar) (lhs rhs : Element Scalar Loose) :
    NativeField.fq_sum_add_product sum lhs rhs
      ⦃ out => sumValue fqPrime fqRadixInverse out =
        (sumValue fqPrime fqRadixInverse sum + decode fqPrime fqRadixInverse lhs.limbs *
          decode fqPrime fqRadixInverse rhs.limbs) % fqPrime ⦄ := by
  unfold NativeField.fq_sum_add_product
  exact fq_product_add_generic_spec sum lhs rhs

#print axioms fq_sum_add_product_spec

@[step]
theorem fq_sum_add_square_spec (sum : Sum Scalar) (value : Element Scalar Loose) :
    NativeField.fq_sum_add_square sum value
      ⦃ out => sumValue fqPrime fqRadixInverse out =
        (sumValue fqPrime fqRadixInverse sum + decode fqPrime fqRadixInverse value.limbs ^ 2) % fqPrime ⦄ := by
  unfold NativeField.fq_sum_add_square
  exact fq_product_square_generic_spec sum value

#print axioms fq_sum_add_square_spec

@[step]
theorem fq_sum_add_term_spec (sum : Sum Scalar) (term : Element Scalar Loose) :
    NativeField.fq_sum_add_term sum term
      ⦃ out => sumValue fqPrime fqRadixInverse out =
        (sumValue fqPrime fqRadixInverse sum + decode fqPrime fqRadixInverse term.limbs) % fqPrime ⦄ := by
  unfold NativeField.fq_sum_add_term
  exact fq_product_term_generic_spec sum term

#print axioms fq_sum_add_term_spec

@[step]
theorem fq_sum_merge_spec (sum other : Sum Scalar) :
    NativeField.fq_sum_merge sum other
      ⦃ out => sumValue fqPrime fqRadixInverse out =
        (sumValue fqPrime fqRadixInverse sum + sumValue fqPrime fqRadixInverse other) % fqPrime ⦄ := by
  unfold NativeField.fq_sum_merge
  simpa only [fq_native_prime_eq] using product_merge_value_spec fqNativeInst fqNativeParameters fqWideFieldParameters fqRadixInverse sum other

#print axioms fq_sum_merge_spec

@[step]
theorem fq_sum_finish_spec (sum : Sum Scalar) :
    NativeField.fq_sum_finish sum
      ⦃ out => val4 out.limbs < 2 * fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs = sumValue fqPrime fqRadixInverse sum ⦄ := by
  unfold NativeField.fq_sum_finish
  simpa only [fq_native_prime_eq] using
    product_finish_value_spec fqNativeInst fqNativeParameters fqWideFieldParameters fqRadixInverse fq_radix_inverse sum

#print axioms fq_sum_finish_spec

end UdonVerify.Native
