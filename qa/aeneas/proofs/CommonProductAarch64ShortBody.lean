import CommonProductAarch64Primitives
import NativeProductMergeLoop

open Aeneas Std Result
namespace UdonVerify.ProductAarch64
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true

abbrev PairIter (M S T : Type) := core.iter.adapters.zip.Zip
  (core.slice.iter.Iter (Element M S)) (core.slice.iter.Iter (Element M T))

def aarch64Add (wide product : A8) : Result A8 := do
  let (out, carry) ← Native.mergeRaw wide product
  massert (carry = 0#u64)
  ok out

def sliceBody {M S T : Type} (iter : PairIter M S T) (wide : A8) :
    Result (ControlFlow (PairIter M S T × A8) A8) := do
  let (pair, next) ← core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    (core.iter.traits.iterator.IteratorSliceIter (Element M S))
    (core.iter.traits.iterator.IteratorSliceIter (Element M T)) iter
  match pair with
  | none => ok (.done wide)
  | some (lhs, rhs) =>
    let product ← NativeField.zakura_udon.field.pasta.word.multiply_wide lhs.limbs rhs.limbs
    let (out, carry) ← Native.mergeRaw wide product
    massert (carry = 0#u64)
    ok (.cont (next, out))

attribute [local irreducible] Std.bind
  NativeField.zakura_udon.field.pasta.word.multiply_wide
  NativeField.zakura_udon.field.pasta.word.adc

/-- The eight original mutable ADC steps equal the previously proved word chain.
    Both iterator exhaustion and the adapter's final guard are checked here. -/
theorem slice_body_eq {M S T : Type} (iter : PairIter M S T) (wide : A8) :
    CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice_loop0.body iter wide =
      sliceBody iter wide := by
  unfold CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice_loop0.body sliceBody
  simp only [Bind.bind, aarch64_multiply_wide_bridge]
  congr 1
  funext result
  rcases result with ⟨pair, next⟩
  simp only [Std.uncurry_apply_pair]
  cases pair with
  | none => rfl
  | some pair =>
    rcases pair with ⟨lhs, rhs⟩
    simp only [Std.uncurry_apply_pair]
    congr 1
    funext product
    obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,ha⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : U64,
        wide = Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7] :=
      ⟨wide[0]!,wide[1]!,wide[2]!,wide[3]!,wide[4]!,wide[5]!,wide[6]!,wide[7]!,Native.array_eight_eta wide⟩
    obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,hb⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 : U64,
        product = Array.make 8#usize [b0,b1,b2,b3,b4,b5,b6,b7] :=
      ⟨product[0]!,product[1]!,product[2]!,product[3]!,product[4]!,product[5]!,product[6]!,product[7]!,
        Native.array_eight_eta product⟩
    subst wide product
    unfold Native.mergeRaw
    simp (config := { maxSteps := 1000000 }) [lift, Array.to_slice_mut, Array.to_slice,
      core.slice.Slice.iter_mut, mutableZipCtor,
      _root_.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
      mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
      core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
      _root_.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
      aarch64_adc_bridge, Bind.bind, bind_tc_eq, Std.uncurry, Std.bind_assoc,
      Array.from_slice, Slice.setAtNat]
    with_unfolding_all rfl

#print axioms slice_body_eq
end UdonVerify.ProductAarch64
