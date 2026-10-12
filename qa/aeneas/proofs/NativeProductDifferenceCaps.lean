import NativeProductDifferenceValue
import NativeCanonical

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

@[step]
theorem fp_mul_sub_product_generic_spec {S T U V : Type}
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi)
    (a : Element Base S) (b : Element Base T)
    (c : Element Base U) (d : Element Base V)
    (ha : val4 a.limbs < productRepresentationBound fpPrime ss)
    (hb : val4 b.limbs < productRepresentationBound fpPrime ts)
    (hc : val4 c.limbs < productRepresentationBound fpPrime us)
    (hd : val4 d.limbs < productRepresentationBound fpPrime vs) :
    NativeField.zakura_udon.field.pasta.products.PastaField.mul_sub_product
      fpNativeInst si ti ui vi a b c d
      ⦃ out => val4 out.limbs < 2 * fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs =
          productDifferenceValue fpPrime fpRadixInverse false a b c d ⦄ := by
  simpa only [fp_native_prime_eq] using
    mul_sub_product_value_spec fpNativeInst fpNativeParameters
      si ti ui vi ss ts us vs fpRadixInverse
      (by simpa only [fp_native_prime_eq] using fp_radix_inverse)
      a b c d
      (by simpa only [fp_native_prime_eq] using ha)
      (by simpa only [fp_native_prime_eq] using hb)
      (by simpa only [fp_native_prime_eq] using hc)
      (by simpa only [fp_native_prime_eq] using hd)

#print axioms fp_mul_sub_product_generic_spec

@[step]
theorem fp_mul_sub_product_spec (a b c d : Element Base Loose)
    (ha : val4 a.limbs < 2 * fpPrime) (hb : val4 b.limbs < 2 * fpPrime)
    (hc : val4 c.limbs < 2 * fpPrime) (hd : val4 d.limbs < 2 * fpPrime) :
    NativeField.fp_mul_sub_product a b c d
      ⦃ out => val4 out.limbs < 2 * fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs =
          productDifferenceValue fpPrime fpRadixInverse false a b c d ⦄ := by
  unfold NativeField.fp_mul_sub_product
  exact fp_mul_sub_product_generic_spec looseInst looseInst looseInst looseInst
    productLooseRepresentation productLooseRepresentation
    productLooseRepresentation productLooseRepresentation a b c d
    (by simpa [productRepresentationBound, productLooseRepresentation] using ha)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hb)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hc)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hd)

#print axioms fp_mul_sub_product_spec

@[step]
theorem fp_mul_sub_double_product_generic_spec {S T U V : Type}
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi)
    (a : Element Base S) (b : Element Base T)
    (c : Element Base U) (d : Element Base V)
    (ha : val4 a.limbs < productRepresentationBound fpPrime ss)
    (hb : val4 b.limbs < productRepresentationBound fpPrime ts)
    (hc : val4 c.limbs < productRepresentationBound fpPrime us)
    (hd : val4 d.limbs < productRepresentationBound fpPrime vs) :
    NativeField.zakura_udon.field.pasta.products.PastaField.mul_sub_double_product
      fpNativeInst si ti ui vi a b c d
      ⦃ out => val4 out.limbs < 2 * fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs =
          productDifferenceValue fpPrime fpRadixInverse true a b c d ⦄ := by
  simpa only [fp_native_prime_eq] using
    mul_sub_double_product_value_spec fpNativeInst fpNativeParameters
      si ti ui vi ss ts us vs fpRadixInverse
      (by simpa only [fp_native_prime_eq] using fp_radix_inverse)
      a b c d
      (by simpa only [fp_native_prime_eq] using ha)
      (by simpa only [fp_native_prime_eq] using hb)
      (by simpa only [fp_native_prime_eq] using hc)
      (by simpa only [fp_native_prime_eq] using hd)

#print axioms fp_mul_sub_double_product_generic_spec

@[step]
theorem fp_mul_sub_double_product_spec (a b c d : Element Base Loose)
    (ha : val4 a.limbs < 2 * fpPrime) (hb : val4 b.limbs < 2 * fpPrime)
    (hc : val4 c.limbs < 2 * fpPrime) (hd : val4 d.limbs < 2 * fpPrime) :
    NativeField.fp_mul_sub_double_product a b c d
      ⦃ out => val4 out.limbs < 2 * fpPrime ∧
        decode fpPrime fpRadixInverse out.limbs =
          productDifferenceValue fpPrime fpRadixInverse true a b c d ⦄ := by
  unfold NativeField.fp_mul_sub_double_product
  exact fp_mul_sub_double_product_generic_spec looseInst looseInst looseInst looseInst
    productLooseRepresentation productLooseRepresentation
    productLooseRepresentation productLooseRepresentation a b c d
    (by simpa [productRepresentationBound, productLooseRepresentation] using ha)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hb)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hc)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hd)

#print axioms fp_mul_sub_double_product_spec

@[step]
theorem fq_mul_sub_product_generic_spec {S T U V : Type}
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi)
    (a : Element Scalar S) (b : Element Scalar T)
    (c : Element Scalar U) (d : Element Scalar V)
    (ha : val4 a.limbs < productRepresentationBound fqPrime ss)
    (hb : val4 b.limbs < productRepresentationBound fqPrime ts)
    (hc : val4 c.limbs < productRepresentationBound fqPrime us)
    (hd : val4 d.limbs < productRepresentationBound fqPrime vs) :
    NativeField.zakura_udon.field.pasta.products.PastaField.mul_sub_product
      fqNativeInst si ti ui vi a b c d
      ⦃ out => val4 out.limbs < 2 * fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs =
          productDifferenceValue fqPrime fqRadixInverse false a b c d ⦄ := by
  simpa only [fq_native_prime_eq] using
    mul_sub_product_value_spec fqNativeInst fqNativeParameters
      si ti ui vi ss ts us vs fqRadixInverse
      (by simpa only [fq_native_prime_eq] using fq_radix_inverse)
      a b c d
      (by simpa only [fq_native_prime_eq] using ha)
      (by simpa only [fq_native_prime_eq] using hb)
      (by simpa only [fq_native_prime_eq] using hc)
      (by simpa only [fq_native_prime_eq] using hd)

#print axioms fq_mul_sub_product_generic_spec

@[step]
theorem fq_mul_sub_product_spec (a b c d : Element Scalar Loose)
    (ha : val4 a.limbs < 2 * fqPrime) (hb : val4 b.limbs < 2 * fqPrime)
    (hc : val4 c.limbs < 2 * fqPrime) (hd : val4 d.limbs < 2 * fqPrime) :
    NativeField.fq_mul_sub_product a b c d
      ⦃ out => val4 out.limbs < 2 * fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs =
          productDifferenceValue fqPrime fqRadixInverse false a b c d ⦄ := by
  unfold NativeField.fq_mul_sub_product
  exact fq_mul_sub_product_generic_spec looseInst looseInst looseInst looseInst
    productLooseRepresentation productLooseRepresentation
    productLooseRepresentation productLooseRepresentation a b c d
    (by simpa [productRepresentationBound, productLooseRepresentation] using ha)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hb)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hc)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hd)

#print axioms fq_mul_sub_product_spec

@[step]
theorem fq_mul_sub_double_product_generic_spec {S T U V : Type}
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi)
    (a : Element Scalar S) (b : Element Scalar T)
    (c : Element Scalar U) (d : Element Scalar V)
    (ha : val4 a.limbs < productRepresentationBound fqPrime ss)
    (hb : val4 b.limbs < productRepresentationBound fqPrime ts)
    (hc : val4 c.limbs < productRepresentationBound fqPrime us)
    (hd : val4 d.limbs < productRepresentationBound fqPrime vs) :
    NativeField.zakura_udon.field.pasta.products.PastaField.mul_sub_double_product
      fqNativeInst si ti ui vi a b c d
      ⦃ out => val4 out.limbs < 2 * fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs =
          productDifferenceValue fqPrime fqRadixInverse true a b c d ⦄ := by
  simpa only [fq_native_prime_eq] using
    mul_sub_double_product_value_spec fqNativeInst fqNativeParameters
      si ti ui vi ss ts us vs fqRadixInverse
      (by simpa only [fq_native_prime_eq] using fq_radix_inverse)
      a b c d
      (by simpa only [fq_native_prime_eq] using ha)
      (by simpa only [fq_native_prime_eq] using hb)
      (by simpa only [fq_native_prime_eq] using hc)
      (by simpa only [fq_native_prime_eq] using hd)

#print axioms fq_mul_sub_double_product_generic_spec

@[step]
theorem fq_mul_sub_double_product_spec (a b c d : Element Scalar Loose)
    (ha : val4 a.limbs < 2 * fqPrime) (hb : val4 b.limbs < 2 * fqPrime)
    (hc : val4 c.limbs < 2 * fqPrime) (hd : val4 d.limbs < 2 * fqPrime) :
    NativeField.fq_mul_sub_double_product a b c d
      ⦃ out => val4 out.limbs < 2 * fqPrime ∧
        decode fqPrime fqRadixInverse out.limbs =
          productDifferenceValue fqPrime fqRadixInverse true a b c d ⦄ := by
  unfold NativeField.fq_mul_sub_double_product
  exact fq_mul_sub_double_product_generic_spec looseInst looseInst looseInst looseInst
    productLooseRepresentation productLooseRepresentation
    productLooseRepresentation productLooseRepresentation a b c d
    (by simpa [productRepresentationBound, productLooseRepresentation] using ha)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hb)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hc)
    (by simpa [productRepresentationBound, productLooseRepresentation] using hd)

#print axioms fq_mul_sub_double_product_spec

end UdonVerify.Native
