import CommonProductDotIterBridges
import CommonProductZipTrace

open Aeneas Std Result
namespace UdonVerify.ProductWrappers
open UdonVerify.ProductPairs UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev ExactOps := CommonProductDotIter.ExactIteratorOps

/-- Use this view only for an iterator whose zip method has the standard default body. -/
def defaultExactOps {I Item : Type} (iterator : core.iter.traits.iterator.Iterator I Item)
    (length : I → Result Usize) : ExactOps I Item where
  iteratorInst := iterator
  len := length
  zip := fun into self other => core.iter.traits.iterator.Iterator.zip.trait_default iterator into self other

theorem default_zip_result {I J A B : Type} (left : core.iter.traits.iterator.Iterator I A)
    (right : core.iter.traits.iterator.Iterator J B) (length : I → Result Usize) (il : I) (ir : J) :
    (defaultExactOps left length).zip (core.iter.traits.collect.IntoIterator.Blanket right) il ir =
      ok (⟨il,ir⟩ : core.iter.adapters.zip.Zip I J) := by
  simp [defaultExactOps,core.iter.traits.iterator.Iterator.zip.trait_default,
    core.iter.traits.iterator.Iterator.zip.default,core.iter.traits.collect.IntoIterator.Blanket]

/-- Keep the actual dispatched length, next and zip methods at the public boundary. -/
def dotIter {M S T A B I J : Type} (inst : Modulus M) (left : State S) (right : State T)
    (intoL : core.iter.traits.collect.IntoIterator A (Element M S) I)
    (intoR : core.iter.traits.collect.IntoIterator B (Element M T) J)
    (opsL : ExactOps I (Element M S)) (opsR : ExactOps J (Element M T)) (lhs : A) (rhs : B) :
    Result (Element M Loose) :=
  CommonProductDotIter.field.pasta.products.dot_iter inst left right intoL intoR opsL opsR lhs rhs

/-- This contract refers to the actual zipped trace, including any custom zip behavior. -/
@[step]
theorem dot_iter_trace_value_spec {M S T A B I J : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (intoL : core.iter.traits.collect.IntoIterator A (Element M S) I)
    (intoR : core.iter.traits.collect.IntoIterator B (Element M T) J)
    (opsL : ExactOps I (Element M S)) (opsR : ExactOps J (Element M T))
    (lhs : A) (rhs : B) (il : I) (ir : J) (nl nr : Usize)
    (z : core.iter.adapters.zip.Zip I J) (entries : List (Element M S × Element M T))
    (hintoL : intoL.into_iter lhs = ok il) (hintoR : intoR.into_iter rhs = ok ir)
    (hlenL : opsL.len il = ok nl) (hlenR : opsR.len ir = ok nr) (heq : nl = nr)
    (hzip : opsL.zip (core.iter.traits.collect.IntoIterator.Blanket opsR.iteratorInst) il ir = ok z)
    (trace : FiniteTrace (zipIterator opsL.iteratorInst opsR.iteratorInst) z entries)
    (valid : ValidEntries (val4 params.modulus) s t entries)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1) :
    dotIter (portableDict inst) left right intoL intoR opsL opsR lhs rhs ⦃ out =>
      val4 out.limbs < 2 * val4 params.modulus ∧
        Native.decode (val4 params.modulus) inverse out.limbs =
          decodedPairs (val4 params.modulus) inverse entries ⦄ := by
  unfold dotIter CommonProductDotIter.field.pasta.products.dot_iter
  simp only [hintoL,hintoR,hlenL,hlenR,bind_ok]
  rw [if_pos heq,hzip]
  simp only [bind_ok]
  rw [DotBridge.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair,
    DotBridge.field.pasta.products.PastaField.sum_of_product_pairs]
  exact pair_method_value_spec inst params constants left right s t hs ht
    (core.iter.traits.collect.IntoIterator.Blanket (zipIterator opsL.iteratorInst opsR.iteratorInst))
    z z entries (by simp) trace valid inverse hinverse

/-- With correct length reports and ordinary zip construction, the result uses both input traces. -/
@[step]
theorem dot_iter_value_spec {M S T A B I J : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (intoL : core.iter.traits.collect.IntoIterator A (Element M S) I)
    (intoR : core.iter.traits.collect.IntoIterator B (Element M T) J)
    (opsL : ExactOps I (Element M S)) (opsR : ExactOps J (Element M T))
    (lhs : A) (rhs : B) (il : I) (ir : J) (nl nr : Usize)
    (xs : List (Element M S)) (ys : List (Element M T))
    (hintoL : intoL.into_iter lhs = ok il) (hintoR : intoR.into_iter rhs = ok ir)
    (hlenL : opsL.len il = ok nl) (hlenR : opsR.len ir = ok nr)
    (hsizeL : nl.val = xs.length) (hsizeR : nr.val = ys.length) (hlen : xs.length = ys.length)
    (hzip : opsL.zip (core.iter.traits.collect.IntoIterator.Blanket opsR.iteratorInst) il ir =
      ok (⟨il,ir⟩ : core.iter.adapters.zip.Zip I J))
    (tl : FiniteTrace opsL.iteratorInst il xs) (tr : FiniteTrace opsR.iteratorInst ir ys)
    (ha : ∀ a ∈ xs, val4 a.limbs < stateWeight s * val4 params.modulus)
    (hb : ∀ b ∈ ys, val4 b.limbs < stateWeight t * val4 params.modulus)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1) :
    dotIter (portableDict inst) left right intoL intoR opsL opsR lhs rhs ⦃ out =>
      val4 out.limbs < 2 * val4 params.modulus ∧
        Native.decode (val4 params.modulus) inverse out.limbs =
          rawSum (fun a => Native.decode (val4 params.modulus) inverse a.limbs)
            (fun b => Native.decode (val4 params.modulus) inverse b.limbs) xs ys % val4 params.modulus ⦄ := by
  have heq : nl = nr := by scalar_tac
  have htrace := zip_finite_trace opsL.iteratorInst opsR.iteratorInst il ir xs ys tl tr hlen
  have hvalid := valid_entries_zip (val4 params.modulus) s t xs ys ha hb
  apply WP.spec_mono (dot_iter_trace_value_spec inst params constants left right s t hs ht
    intoL intoR opsL opsR lhs rhs il ir nl nr ⟨il,ir⟩ (xs.zip ys)
    hintoL hintoR hlenL hlenR heq hzip htrace hvalid inverse hinverse)
  intro out hout
  exact ⟨hout.1,hout.2.trans (decoded_pairs_zip _ _ xs ys)⟩

theorem dot_iter_reported_lengths_mismatch {M S T A B I J : Type}
    (inst : Modulus M) (left : State S) (right : State T)
    (intoL : core.iter.traits.collect.IntoIterator A (Element M S) I)
    (intoR : core.iter.traits.collect.IntoIterator B (Element M T) J)
    (opsL : ExactOps I (Element M S)) (opsR : ExactOps J (Element M T))
    (lhs : A) (rhs : B) (il : I) (ir : J) (nl nr : Usize)
    (hintoL : intoL.into_iter lhs = ok il) (hintoR : intoR.into_iter rhs = ok ir)
    (hlenL : opsL.len il = ok nl) (hlenR : opsR.len ir = ok nr) (hne : nl ≠ nr) :
    dotIter inst left right intoL intoR opsL opsR lhs rhs = fail Error.panic := by
  unfold dotIter CommonProductDotIter.field.pasta.products.dot_iter
  simp [hintoL,hintoR,hlenL,hlenR,hne,core.fmt.Arguments.from_str]

theorem dot_iter_lengths_mismatch {M S T A B I J : Type}
    (inst : Modulus M) (left : State S) (right : State T)
    (intoL : core.iter.traits.collect.IntoIterator A (Element M S) I)
    (intoR : core.iter.traits.collect.IntoIterator B (Element M T) J)
    (opsL : ExactOps I (Element M S)) (opsR : ExactOps J (Element M T))
    (lhs : A) (rhs : B) (il : I) (ir : J) (nl nr : Usize)
    (xs : List (Element M S)) (ys : List (Element M T))
    (hintoL : intoL.into_iter lhs = ok il) (hintoR : intoR.into_iter rhs = ok ir)
    (hlenL : opsL.len il = ok nl) (hlenR : opsR.len ir = ok nr)
    (hsizeL : nl.val = xs.length) (hsizeR : nr.val = ys.length) (hne : xs.length ≠ ys.length) :
    dotIter inst left right intoL intoR opsL opsR lhs rhs = fail Error.panic := by
  apply dot_iter_reported_lengths_mismatch inst left right intoL intoR opsL opsR
    lhs rhs il ir nl nr hintoL hintoR hlenL hlenR
  intro heq
  apply hne
  rw [←hsizeL,←hsizeR,heq]

#print axioms default_zip_result
#print axioms dot_iter_trace_value_spec
#print axioms dot_iter_value_spec
#print axioms dot_iter_reported_lengths_mismatch
#print axioms dot_iter_lengths_mismatch
end UdonVerify.ProductWrappers
