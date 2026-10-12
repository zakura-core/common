import CommonProductPortableShortBody

open Aeneas Std Result
namespace UdonVerify.ProductPortable
open UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def remaining {M S T : Type} (iter : PairIter M S T) : Nat :=
  rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs)
    (iter.fst.slice.val.drop iter.fst.i) (iter.snd.slice.val.drop iter.snd.i)

theorem pair_next_some_eq {M S T : Type} (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (i : Nat) (ha : i < lhs.length) (hb : i < rhs.length) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (Element M S))
      (core.iter.traits.iterator.IteratorSliceIter (Element M T))
      ⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ =
      ok (some (lhs[i]'ha,rhs[i]'hb),⟨⟨lhs,i+1⟩,⟨rhs,i+1⟩⟩) := by
  simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next, ha, hb]
  constructor <;> rfl

theorem pair_next_none_eq {M S T : Type} (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (i : Nat) (ha : lhs.length ≤ i) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (Element M S))
      (core.iter.traits.iterator.IteratorSliceIter (Element M T))
      ⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ = ok (none,⟨⟨lhs,i⟩,⟨rhs,i⟩⟩) := by
  simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next,
    show ¬ i < lhs.length by omega]

theorem remaining_step {M S T : Type} (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (i : Nat) (ha : i < lhs.length) (hb : i < rhs.length) :
    remaining (⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ : PairIter M S T) =
      val4 (lhs[i]'ha).limbs * val4 (rhs[i]'hb).limbs +
        remaining (⟨⟨lhs,i+1⟩,⟨rhs,i+1⟩⟩ : PairIter M S T) := by
  unfold remaining
  dsimp only
  rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb]
  rfl

@[step]
theorem portable_add_spec (wide product : A8) (hbound : val8 wide + val8 product < R ^ 2) :
    portableAdd wide product ⦃ out => val8 out = val8 wide + val8 product ⦄ := by
  unfold portableAdd
  obtain ⟨pair,hraw,hpair⟩ := WP.spec_imp_exists (Native.merge_raw_spec wide product)
  rcases pair with ⟨out,carry⟩
  rcases hpair with ⟨hcarry,hvalue⟩
  dsimp only at hvalue
  rw [hraw]
  simp only [bind_ok, Std.uncurry_apply_pair]
  have hzeroVal : carry.val = 0 := by
    norm_num [R, B] at hvalue hbound
    omega
  have hzero : carry = 0#u64 := by scalar_tac
  subst carry
  simpa [Std.uncurry, massert, WP.spec_ok] using hvalue

@[step]
theorem slice_body_some_spec {M S T : Type} (iter next : PairIter M S T) (wide : A8)
    (lhs : Element M S) (rhs : Element M T)
    (hnext : core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (Element M S))
      (core.iter.traits.iterator.IteratorSliceIter (Element M T)) iter = ok (some (lhs,rhs),next))
    (hbound : val8 wide + val4 lhs.limbs * val4 rhs.limbs < R ^ 2) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop0.body iter wide
      ⦃ flow => ∃ out, flow = .cont (next,out) ∧
        val8 out = val8 wide + val4 lhs.limbs * val4 rhs.limbs ⦄ := by
  rw [slice_body_eq]
  unfold sliceBody
  rw [hnext]
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [Native.wide_multiply_eq]
  step -grind with (slice_multiply_wide_spec lhs.limbs rhs.limbs) as ⟨product,hproduct⟩
  have hb : val8 wide + val8 product < R ^ 2 := by simpa only [hproduct] using hbound
  apply WP.spec_bind (Native.merge_raw_spec wide product)
  intro pair hpair
  rcases pair with ⟨out,carry⟩
  rcases hpair with ⟨hcarry,hvalue⟩
  dsimp only at hvalue
  have hzeroVal : carry.val = 0 := by
    norm_num [R, B] at hvalue hb
    omega
  have hzero : carry = 0#u64 := by scalar_tac
  subst carry
  step -grind
  exact ⟨out,rfl,by simpa only [hproduct, show (0#u64).val = 0 from rfl,
    Nat.mul_zero, Nat.add_zero] using hvalue⟩

#print axioms pair_next_some_eq
#print axioms pair_next_none_eq
#print axioms remaining_step
#print axioms portable_add_spec
#print axioms slice_body_some_spec
end UdonVerify.ProductPortable
