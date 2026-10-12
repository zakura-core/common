import CommonProductPortableLanes
import CommonProductPortableShortSteps

open Aeneas Std Result
namespace UdonVerify.ProductPortable
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def remainderBody {M S T : Type} (inst : Modulus M) (iter : PairIter M S T) (lanes : Lanes M) :
    Result (ControlFlow (PairIter M S T × Lanes M) (Lanes M)) := do
  let (pair,next) ← core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    (core.iter.traits.iterator.IteratorSliceIter (Element M S))
    (core.iter.traits.iterator.IteratorSliceIter (Element M T)) iter
  match pair with
  | none => ok (.done lanes)
  | some (lhs,rhs) =>
    let updated ← CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner true inst lanes[0]! lhs rhs
    ok (.cont (next,lanes.set 0#usize updated))

attribute [local irreducible] Std.bind
  CommonProductsPortable.field.pasta.products.ProductSum.add_product_inner

theorem remainder_body_eq {M S T : Type} (inst : Modulus M) (iter : PairIter M S T) (lanes : Lanes M) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3.body inst iter lanes =
      remainderBody inst iter lanes := by
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3.body remainderBody
  simp only [Bind.bind]
  congr 1
  funext result
  rcases result with ⟨pair,next⟩
  simp only [Std.uncurry_apply_pair]
  cases pair with
  | none => rfl
  | some pair =>
    rcases pair with ⟨lhs,rhs⟩
    simp only [Std.uncurry_apply_pair]
    rw [array_four_eta_generic lanes]
    simp [Array.index_mut_usize, Array.index_usize, Array.getElem!_Nat_eq, Bind.bind,
      Std.bind_assoc, Array.set]

/-- Replacing lane zero changes only its contribution to the sum. -/
theorem lanes_set_zero_value {M : Type} (lanes : Lanes M) (value : Sum M) :
    lanesInteger (lanes.set 0#usize value) + sumInteger lanes[0]! =
      lanesInteger lanes + sumInteger value := by
  rw [array_four_eta_generic lanes]
  simp [lanesInteger,Array.set,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

#print axioms remainder_body_eq
#print axioms lanes_set_zero_value
end UdonVerify.ProductPortable
