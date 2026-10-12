import NativeProductDifference
import NativeSubtract

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem decoded_product_difference (p inverse a b c d out factor : Nat) (hp : 0 < p)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hcert : Nat.ModEq p (R * out + factor * (c * d)) (a * b)) :
    (out * inverse) % p =
      (((a * inverse) % p * ((b * inverse) % p)) % p + p -
        (factor * ((c * inverse) % p * ((d * inverse) % p))) % p) % p := by
  have hscaled : Nat.ModEq p
      ((R * inverse) * (out * inverse) + factor * ((c * inverse) * (d * inverse)))
      ((a * inverse) * (b * inverse)) := by
    convert hcert.mul_right (inverse ^ 2) using 1 <;> ring
  have hcancel : Nat.ModEq p ((R * inverse) * (out * inverse)) (out * inverse) := by
    simpa only [one_mul] using hinverse.mul_right (out * inverse)
  have hordinary : Nat.ModEq p
      (out * inverse + factor * ((c * inverse) * (d * inverse)))
      ((a * inverse) * (b * inverse)) :=
    (hcancel.add_right (factor * ((c * inverse) * (d * inverse)))).symm.trans hscaled
  have h := decoded_difference p 1 ((a * inverse) * (b * inverse))
    (factor * ((c * inverse) * (d * inverse))) (out * inverse) hp hordinary
  simpa only [mul_one, Nat.mul_mod, Nat.mod_mod] using h

def productDifferenceValue {M S T U V : Type} (p inverse : Nat) (double : Bool)
    (a : Element M S) (b : Element M T) (c : Element M U) (d : Element M V) : Nat :=
  ((decode p inverse a.limbs * decode p inverse b.limbs) % p + p -
    (productScale double * (decode p inverse c.limbs * decode p inverse d.limbs)) % p) % p

@[step]
theorem product_difference_value_spec {M S T U V : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (double : Bool) (a : Element M S) (b : Element M T)
    (c : Element M U) (d : Element M V)
    (ha : val4 a.limbs < productRepresentationBound (val4 params.modulus) ss)
    (hb : val4 b.limbs < productRepresentationBound (val4 params.modulus) ts)
    (hc : val4 c.limbs < productRepresentationBound (val4 params.modulus) us)
    (hd : val4 d.limbs < productRepresentationBound (val4 params.modulus) vs) :
    NativeField.zakura_udon.field.pasta.products.PastaField.product_difference
      double inst si ti ui vi a b c d
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs =
          productDifferenceValue (val4 params.modulus) inverse double a b c d ⦄ := by
  step -grind with (product_difference_spec inst params si ti ui vi ss ts us vs
    double a b c d ha hb hc hd) as ⟨out, hbound, hcert⟩
  exact ⟨hbound, decoded_product_difference _ _ _ _ _ _ _ _ params.positive hinverse hcert⟩

@[step]
theorem mul_sub_product_value_spec {M S T U V : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (a : Element M S) (b : Element M T) (c : Element M U) (d : Element M V)
    (ha : val4 a.limbs < productRepresentationBound (val4 params.modulus) ss)
    (hb : val4 b.limbs < productRepresentationBound (val4 params.modulus) ts)
    (hc : val4 c.limbs < productRepresentationBound (val4 params.modulus) us)
    (hd : val4 d.limbs < productRepresentationBound (val4 params.modulus) vs) :
    NativeField.zakura_udon.field.pasta.products.PastaField.mul_sub_product inst si ti ui vi a b c d
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs =
          productDifferenceValue (val4 params.modulus) inverse false a b c d ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.PastaField.mul_sub_product
  exact product_difference_value_spec inst params si ti ui vi ss ts us vs inverse hinverse
    false a b c d ha hb hc hd

@[step]
theorem mul_sub_double_product_value_spec {M S T U V : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (a : Element M S) (b : Element M T) (c : Element M U) (d : Element M V)
    (ha : val4 a.limbs < productRepresentationBound (val4 params.modulus) ss)
    (hb : val4 b.limbs < productRepresentationBound (val4 params.modulus) ts)
    (hc : val4 c.limbs < productRepresentationBound (val4 params.modulus) us)
    (hd : val4 d.limbs < productRepresentationBound (val4 params.modulus) vs) :
    NativeField.zakura_udon.field.pasta.products.PastaField.mul_sub_double_product inst si ti ui vi a b c d
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        decode (val4 params.modulus) inverse out.limbs =
          productDifferenceValue (val4 params.modulus) inverse true a b c d ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.PastaField.mul_sub_double_product
  exact product_difference_value_spec inst params si ti ui vi ss ts us vs inverse hinverse
    true a b c d ha hb hc hd

#print axioms decoded_product_difference
#print axioms product_difference_value_spec
#print axioms mul_sub_product_value_spec
#print axioms mul_sub_double_product_value_spec

end UdonVerify.Native
