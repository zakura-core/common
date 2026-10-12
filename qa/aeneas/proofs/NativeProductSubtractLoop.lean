import NativeProductWords
open Aeneas Std Result
open NativeField.zakura_udon.field.pasta.products.PastaField
namespace UdonVerify.Native
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem product_sbb_result (lhs rhs borrow : U64) (hborrow : borrow.val ≤ 1) :
    ∃ lo hi : U64,
      NativeField.zakura_udon.field.pasta.word.sbb lhs rhs borrow = ok (lo,hi) ∧
      hi.val ≤ 1 ∧ lo.val+rhs.val+borrow.val=lhs.val+B*hi.val := by
  obtain ⟨pair,hresult,hbound,hvalue⟩ := WP.spec_imp_exists (slice_sbb_identity lhs rhs borrow hborrow)
  rcases pair with ⟨lo,hi⟩
  exact ⟨lo,hi,by rw [sbb_eq];exact hresult,hbound,hvalue⟩

theorem product_subtract_loop_unfold (it : WideZip) (back : WideZip → WideZip) (borrow : U64) :
    product_difference_loop1 it back borrow = (do
      let flow ← product_difference_loop1.body it back borrow
      match flow with
      | .done out => ok out
      | .cont (it',back',borrow') => product_difference_loop1 it' back' borrow') := by
  unfold product_difference_loop1
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont state => rcases state with ⟨it',back',borrow'⟩;rfl

@[step]
theorem product_subtract_loop_spec_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : U64) :
    product_difference_loop1 ⟨⟨Slice.from [a0,a1,a2,a3,a4,a5,a6,a7] (by scalar_tac),0⟩,
      ⟨Slice.from [b0,b1,b2,b3,b4,b5,b6,b7] (by scalar_tac),0⟩⟩ (fun z => z) 0#u64
      ⦃ borrow back => borrow.val ≤ 1 ∧
        val8 (Array.from_slice (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])
          (back ⟨⟨Slice.from [a0,a1,a2,a3,a4,a5,a6,a7] (by scalar_tac),0⟩,
            ⟨Slice.from [b0,b1,b2,b3,b4,b5,b6,b7] (by scalar_tac),0⟩⟩).fst.slice)
          + val8 (Array.make 8#usize [b0,b1,b2,b3,b4,b5,b6,b7]) =
        val8 (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])+R^2*borrow.val ⦄ := by
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [sbb_eq]
  step -grind with (slice_sbb_identity _ _ 0#u64 (by decide)) as ⟨pair0,hb0,h0⟩
  rcases pair0 with ⟨r0,c0⟩
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [sbb_eq]
  step -grind with (slice_sbb_identity _ _ c0 hb0) as ⟨pair1,hb1,h1⟩
  rcases pair1 with ⟨r1,c1⟩
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [sbb_eq]
  step -grind with (slice_sbb_identity _ _ c1 hb1) as ⟨pair2,hb2,h2⟩
  rcases pair2 with ⟨r2,c2⟩
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [sbb_eq]
  step -grind with (slice_sbb_identity _ _ c2 hb2) as ⟨pair3,hb3,h3⟩
  rcases pair3 with ⟨r3,c3⟩
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [sbb_eq]
  step -grind with (slice_sbb_identity _ _ c3 hb3) as ⟨pair4,hb4,h4⟩
  rcases pair4 with ⟨r4,c4⟩
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [sbb_eq]
  step -grind with (slice_sbb_identity _ _ c4 hb4) as ⟨pair5,hb5,h5⟩
  rcases pair5 with ⟨r5,c5⟩
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [sbb_eq]
  step -grind with (slice_sbb_identity _ _ c5 hb5) as ⟨pair6,hb6,h6⟩
  rcases pair6 with ⟨r6,c6⟩
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [sbb_eq]
  step -grind with (slice_sbb_identity _ _ c6 hb6) as ⟨pair7,hb7,h7⟩
  rcases pair7 with ⟨r7,c7⟩
  simp only [bind_ok, Std.uncurry_apply_pair]
  rw [product_subtract_loop_unfold]
  unfold product_difference_loop1.body
  simp [Slice.getElem_Nat_eq, mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, WP.spec_ok]
  change r0.val+b0.val+0=a0.val+B*c0.val at h0
  change r1.val+b1.val+c0.val=a1.val+B*c1.val at h1
  change r2.val+b2.val+c1.val=a2.val+B*c2.val at h2
  change r3.val+b3.val+c2.val=a3.val+B*c3.val at h3
  change r4.val+b4.val+c3.val=a4.val+B*c4.val at h4
  change r5.val+b5.val+c4.val=a5.val+B*c5.val at h5
  change r6.val+b6.val+c5.val=a6.val+B*c6.val at h6
  change r7.val+b7.val+c6.val=a7.val+B*c7.val at h7
  refine ⟨hb7,?_⟩
  simp [val8,Array.from_slice,Slice.setAtNat]
  unfold R
  linear_combination h0+B*h1+B^2*h2+B^3*h3+B^4*h4+B^5*h5+B^6*h6+B^7*h7

@[step]
theorem product_subtract_loop_spec (wide product : A8) :
    product_difference_loop1 ⟨⟨wide.to_slice,0⟩,⟨product.to_slice,0⟩⟩ (fun z => z) 0#u64
      ⦃ borrow back => borrow.val ≤ 1 ∧
        val8 (Array.from_slice wide (back ⟨⟨wide.to_slice,0⟩,⟨product.to_slice,0⟩⟩).fst.slice)
          + val8 product = val8 wide+R^2*borrow.val ⦄ := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,ha⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : U64,
      wide=Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7] :=
    ⟨wide[0]!,wide[1]!,wide[2]!,wide[3]!,wide[4]!,wide[5]!,wide[6]!,wide[7]!,array_eight_eta wide⟩
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,hb⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 : U64,
      product=Array.make 8#usize [b0,b1,b2,b3,b4,b5,b6,b7] :=
    ⟨product[0]!,product[1]!,product[2]!,product[3]!,product[4]!,product[5]!,product[6]!,product[7]!,array_eight_eta product⟩
  subst wide product
  simpa [Array.to_slice] using product_subtract_loop_spec_eight a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7

#print axioms product_sbb_result
#print axioms product_subtract_loop_unfold
#print axioms product_subtract_loop_spec_eight
#print axioms product_subtract_loop_spec
end UdonVerify.Native
