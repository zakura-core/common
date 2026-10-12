import CommonProductAarch64ShortAPI

open Aeneas Std Result
namespace UdonVerify.ProductAarch64
open UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def decodedSum {M S T : Type} (p inverse : Nat)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) : Nat :=
  rawSum (fun a => Native.decode p inverse a.limbs)
    (fun b => Native.decode p inverse b.limbs) lhs.val rhs.val % p

@[step]
theorem slice_short_value_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (left : State S) (right : State T)
    (s t : Bool) (hs : left.sealedSealedInst.REDUCED = ok s)
    (ht : right.sealedSealedInst.REDUCED = ok t)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length) (hshort : lhs.length ≤ 3)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < stateWeight s * val4 params.modulus)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < stateWeight t * val4 params.modulus)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1) :
    CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice
      (aarch64Dict inst) left right lhs rhs ⦃ out =>
        val4 out.limbs < 2 * val4 params.modulus ∧
        Native.decode (val4 params.modulus) inverse out.limbs =
          decodedSum (val4 params.modulus) inverse lhs rhs ⦄ := by
  apply WP.spec_mono (slice_short_spec inst params left right s t hs ht lhs rhs hlen hshort ha hb)
  intro out hout
  refine ⟨hout.1,?_⟩
  have hscaled := Native.decoded_product_sum _ _ _ _ hinverse hout.2
  have hdecoded := raw_sum_decoded (fun a => val4 a.limbs) (fun b => val4 b.limbs)
    (val4 params.modulus) inverse lhs.val rhs.val
  exact hscaled.trans hdecoded.symm

theorem slice_lengths_mismatch {M S T : Type} (inst : Modulus M) (left : State S) (right : State T)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length ≠ rhs.length) :
    CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice inst left right lhs rhs =
      fail Error.panic := by
  have hne : Aeneas.Std.Slice.len lhs ≠ Aeneas.Std.Slice.len rhs := by
    intro h
    exact hlen (by simpa using congrArg UScalar.val h)
  unfold CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice
  simp [hne, massert, core.fmt.Arguments.from_str]

#print axioms slice_short_value_spec
#print axioms slice_lengths_mismatch
end UdonVerify.ProductAarch64
