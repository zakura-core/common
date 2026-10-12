import NativeSmallLoop
import NativeIterator
open Aeneas Std Result
open NativeField.zakura_udon.field.pasta.small
namespace UdonVerify.Native
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
abbrev RepairZip := core.iter.adapters.zip.Zip (core.slice.iter.IterMut U64)
  (core.array.iter.IntoIter U64 4#usize)

theorem native_adc_eq (a b c : U64) :
    NativeField.zakura_udon.field.pasta.word.adc a b c =
      udon_kernel_slice.field.pasta.word.adc a b c := by rfl

theorem small_repair_unfold (iter : RepairZip) (back : RepairZip → RepairZip) (carry : U64) :
    multiply_loop0_loop0 iter back carry = (do
      let r ← multiply_loop0_loop0.body iter back carry
      match r with
      | .done out => ok out
      | .cont (it,b,c) => multiply_loop0_loop0 it b c) := by
  unfold multiply_loop0_loop0
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨it,b,c⟩; rfl

@[step]
theorem small_repair_loop_spec_four (a0 a1 a2 a3 b0 b1 b2 b3 : U64) :
    multiply_loop0_loop0
      ⟨⟨Slice.from [a0,a1,a2,a3] (by scalar_tac),0⟩,
       ⟨Slice.from [b0,b1,b2,b3] (by scalar_tac),0⟩⟩ (fun z => z) 0#u64
      ⦃ z back => ∃ carry : Nat, carry≤1 ∧
        val4 (Array.from_slice (Array.make 4#usize [a0,a1,a2,a3]) (back z).fst.slice)
          + R*carry = val4 (Array.make 4#usize [a0,a1,a2,a3])
            + val4 (Array.make 4#usize [b0,b1,b2,b3]) ⦄ := by
  rw [small_repair_unfold]
  unfold multiply_loop0_loop0.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  rw [native_adc_eq]
  step -grind with slice_adc_identity as ⟨pair0,h0⟩
  rcases pair0 with ⟨r0,c0⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [small_repair_unfold]
  unfold multiply_loop0_loop0.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  rw [native_adc_eq]
  step -grind with slice_adc_identity as ⟨pair1,h1⟩
  rcases pair1 with ⟨r1,c1⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [small_repair_unfold]
  unfold multiply_loop0_loop0.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  rw [native_adc_eq]
  step -grind with slice_adc_identity as ⟨pair2,h2⟩
  rcases pair2 with ⟨r2,c2⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [small_repair_unfold]
  unfold multiply_loop0_loop0.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  rw [native_adc_eq]
  step -grind with slice_adc_identity as ⟨pair3,h3⟩
  rcases pair3 with ⟨r3,c3⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [small_repair_unfold]
  unfold multiply_loop0_loop0.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc, WP.spec_ok]
  change r0.val+B*c0.val=a0.val+b0.val+0 at h0
  change r1.val+B*c1.val=a1.val+b1.val+c0.val at h1
  change r2.val+B*c2.val=a2.val+b2.val+c1.val at h2
  change r3.val+B*c3.val=a3.val+b3.val+c2.val at h3
  have hc0 : c0.val≤1 := by
    have h := h0
    norm_num only [B] at h
    scalar_tac
  have hc1 : c1.val≤1 := by
    have h := h1
    norm_num only [B] at h
    scalar_tac
  have hc2 : c2.val≤1 := by
    have h := h2
    norm_num only [B] at h
    scalar_tac
  have hc3 : c3.val≤1 := by
    have h := h3
    norm_num only [B] at h
    scalar_tac
  refine ⟨c3.val,hc3,?_⟩
  rw [small_restore_four]
  simp [val4]
  unfold R
  linear_combination h0+B*h1+B^2*h2+B^3*h3

@[step]
theorem small_repair_loop_spec (a b : A4) :
    multiply_loop0_loop0 ⟨⟨a.to_slice,0⟩,⟨b.to_slice,0⟩⟩ (fun z => z) 0#u64
      ⦃ z back => ∃ carry : Nat, carry≤1 ∧
        val4 (Array.from_slice a (back z).fst.slice)+R*carry=val4 a+val4 b ⦄ := by
  obtain ⟨a0,a1,a2,a3,ha⟩ : ∃ a0 a1 a2 a3 : U64,
      a=Array.make 4#usize [a0,a1,a2,a3] :=
    ⟨a[0]!,a[1]!,a[2]!,a[3]!,CommonVerify.array_four_eta a⟩
  obtain ⟨b0,b1,b2,b3,hb⟩ : ∃ b0 b1 b2 b3 : U64,
      b=Array.make 4#usize [b0,b1,b2,b3] :=
    ⟨b[0]!,b[1]!,b[2]!,b[3]!,CommonVerify.array_four_eta b⟩
  subst a b
  simpa [Array.to_slice] using small_repair_loop_spec_four a0 a1 a2 a3 b0 b1 b2 b3

#print axioms native_adc_eq
#print axioms small_repair_unfold
#print axioms small_repair_loop_spec_four
#print axioms small_repair_loop_spec
end UdonVerify.Native
