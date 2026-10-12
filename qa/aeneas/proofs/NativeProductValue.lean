import NativeProductInner
import NativeProductComposed
import NativeProductTerm
import NativeProductFinish

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem product_add_product_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (sum : Sum M) (lhs : Element M S) (rhs : Element M T) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_product inst sum lhs rhs
      ⦃ out => Nat.ModEq (val4 params.modulus) (sumInteger out)
        (sumInteger sum + val4 lhs.limbs * val4 rhs.limbs) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.ProductSum.add_product
  step -grind with (product_inner_spec false inst params constants sum lhs rhs (by simp))
    as ⟨out, hout, hbounded⟩
  exact hout

theorem decoded_accumulated_product (p inverse total a b value : Nat)
    (hmod : Nat.ModEq p value (total + a * b)) :
    (value * inverse ^ 2) % p =
      ((total * inverse ^ 2) % p + (a * inverse) % p * ((b * inverse) % p)) % p := by
  calc
    _ = ((total + a * b) * inverse ^ 2) % p := hmod.mul_right _
    _ = (total * inverse ^ 2 + (a * inverse) * (b * inverse)) % p := by congr 1; ring
    _ = _ := by simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem decoded_accumulated_square (p inverse total a value : Nat)
    (hmod : Nat.ModEq p value (total + a ^ 2)) :
    (value * inverse ^ 2) % p =
      ((total * inverse ^ 2) % p + ((a * inverse) % p) ^ 2) % p := by
  simpa only [pow_two] using decoded_accumulated_product p inverse total a a value
    (by simpa only [pow_two] using hmod)

theorem decoded_accumulated_term (p inverse total a value : Nat)
    (hinverse : Nat.ModEq p (R * inverse) 1)
    (hmod : Nat.ModEq p value (total + R * a)) :
    (value * inverse ^ 2) % p =
      ((total * inverse ^ 2) % p + (a * inverse) % p) % p := by
  have hscaled : Nat.ModEq p (value * inverse ^ 2)
      (total * inverse ^ 2 + (R * inverse) * (a * inverse)) := by
    convert hmod.mul_right (inverse ^ 2) using 1 <;> ring
  have hterm : Nat.ModEq p (total * inverse ^ 2 + (R * inverse) * (a * inverse))
      (total * inverse ^ 2 + a * inverse) := by
    simpa only [one_mul] using (hinverse.mul_right (a * inverse)).add_left (total * inverse ^ 2)
  exact (hscaled.trans hterm).trans (Nat.add_mod _ _ _)

theorem decoded_accumulated_merge (p inverse left right value : Nat)
    (hmod : Nat.ModEq p value (left + right)) :
    (value * inverse ^ 2) % p =
      ((left * inverse ^ 2) % p + (right * inverse ^ 2) % p) % p := by
  calc
    _ = ((left + right) * inverse ^ 2) % p := hmod.mul_right _
    _ = (left * inverse ^ 2 + right * inverse ^ 2) % p := by congr 1; ring
    _ = _ := Nat.add_mod _ _ _

@[step]
theorem product_add_product_value_spec {M S T : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (inverse : Nat) (sum : Sum M) (lhs : Element M S) (rhs : Element M T) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_product inst sum lhs rhs
      ⦃ out => sumValue (val4 params.modulus) inverse out =
        (sumValue (val4 params.modulus) inverse sum +
          decode (val4 params.modulus) inverse lhs.limbs *
            decode (val4 params.modulus) inverse rhs.limbs) % val4 params.modulus ⦄ := by
  step -grind with (product_add_product_spec inst params constants sum lhs rhs) as ⟨out, hout⟩
  exact decoded_accumulated_product _ _ _ _ _ _ hout

@[step]
theorem product_add_square_value_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (inverse : Nat) (sum : Sum M) (value : Element M S) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_square inst sum value
      ⦃ out => sumValue (val4 params.modulus) inverse out =
        (sumValue (val4 params.modulus) inverse sum +
          decode (val4 params.modulus) inverse value.limbs ^ 2) % val4 params.modulus ⦄ := by
  step -grind with (product_add_square_spec inst params constants sum value) as ⟨out, hout⟩
  exact decoded_accumulated_square _ _ _ _ _ hout

@[step]
theorem product_add_term_value_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (sum : Sum M) (term : Element M S) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_term inst sum term
      ⦃ out => sumValue (val4 params.modulus) inverse out =
        (sumValue (val4 params.modulus) inverse sum +
          decode (val4 params.modulus) inverse term.limbs) % val4 params.modulus ⦄ := by
  step -grind with (product_add_term_spec inst params constants sum term) as ⟨out, hout⟩
  exact decoded_accumulated_term _ _ _ _ _ hinverse hout

@[step]
theorem product_merge_value_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (inverse : Nat) (sum other : Sum M) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.merge inst sum other
      ⦃ out => sumValue (val4 params.modulus) inverse out =
        (sumValue (val4 params.modulus) inverse sum +
          sumValue (val4 params.modulus) inverse other) % val4 params.modulus ⦄ := by
  step -grind with (product_merge_spec inst params constants sum other) as ⟨out, hout⟩
  exact decoded_accumulated_merge _ _ _ _ _ hout

#print axioms product_add_product_spec
#print axioms decoded_accumulated_product
#print axioms decoded_accumulated_square
#print axioms decoded_accumulated_term
#print axioms decoded_accumulated_merge
#print axioms product_add_product_value_spec
#print axioms product_add_square_value_spec
#print axioms product_add_term_value_spec
#print axioms product_merge_value_spec

end UdonVerify.Native
