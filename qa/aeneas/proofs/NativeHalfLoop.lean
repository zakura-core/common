import NativeSmallRepair
open Aeneas Std Result
open NativeField.zakura_udon.field.pasta.PastaField
namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem half_loop_unfold (iter : RepairZip) (back : RepairZip → RepairZip)
    (mask carry : U64) : half_loop iter back mask carry = (do
      let r ← half_loop.body mask iter back carry
      match r with
      | .done out => ok out
      | .cont (it,b,c) => half_loop it b mask c) := by
  unfold half_loop
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨it,b,c⟩; rfl

@[step]
theorem half_loop_spec_four (mask a0 a1 a2 a3 b0 b1 b2 b3 : U64) :
    half_loop ⟨⟨Slice.from [a0,a1,a2,a3] (by scalar_tac),0⟩,
       ⟨Slice.from [b0,b1,b2,b3] (by scalar_tac),0⟩⟩ (fun z => z) mask 0#u64
      ⦃ carry z => carry.val≤1 ∧
        val4 (Array.from_slice (Array.make 4#usize [a0,a1,a2,a3]) z.fst.slice)
          + R*carry.val = val4 (Array.make 4#usize [a0,a1,a2,a3]) +
            val4 (Array.make 4#usize [b0 &&& mask,b1 &&& mask,b2 &&& mask,b3 &&& mask]) ⦄ := by
  rw [half_loop_unfold]
  unfold half_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  step -grind with UScalar.and_spec as ⟨m0,hm0,hmb0⟩
  rw [native_adc_eq]
  step -grind with slice_adc_identity as ⟨pair0,h0⟩
  rcases pair0 with ⟨r0,c0⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [half_loop_unfold]
  unfold half_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  step -grind with UScalar.and_spec as ⟨m1,hm1,hmb1⟩
  rw [native_adc_eq]
  step -grind with slice_adc_identity as ⟨pair1,h1⟩
  rcases pair1 with ⟨r1,c1⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [half_loop_unfold]
  unfold half_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  step -grind with UScalar.and_spec as ⟨m2,hm2,hmb2⟩
  rw [native_adc_eq]
  step -grind with slice_adc_identity as ⟨pair2,h2⟩
  rcases pair2 with ⟨r2,c2⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [half_loop_unfold]
  unfold half_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    Std.bind_assoc]
  step -grind with UScalar.and_spec as ⟨m3,hm3,hmb3⟩
  rw [native_adc_eq]
  step -grind with slice_adc_identity as ⟨pair3,h3⟩
  rcases pair3 with ⟨r3,c3⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [half_loop_unfold]
  unfold half_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next,
    WP.spec_ok]
  change r0.val+B*c0.val=a0.val+m0.val+0 at h0
  change m0.val=(b0 &&& mask).val at hm0
  change r1.val+B*c1.val=a1.val+m1.val+c0.val at h1
  change m1.val=(b1 &&& mask).val at hm1
  change r2.val+B*c2.val=a2.val+m2.val+c1.val at h2
  change m2.val=(b2 &&& mask).val at hm2
  change r3.val+B*c3.val=a3.val+m3.val+c2.val at h3
  change m3.val=(b3 &&& mask).val at hm3
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
  refine ⟨hc3,?_⟩
  rw [small_restore_four]
  simp [val4]
  simp only [UScalar.val_and] at hm0 hm1 hm2 hm3
  rw [←hm0,←hm1,←hm2,←hm3]
  unfold R
  linear_combination h0+B*h1+B^2*h2+B^3*h3

@[step]
theorem half_loop_spec (mask : U64) (a b : A4) :
    half_loop ⟨⟨a.to_slice,0⟩,⟨b.to_slice,0⟩⟩ (fun z => z) mask 0#u64
      ⦃ carry z => carry.val≤1 ∧
        val4 (Array.from_slice a z.fst.slice)+R*carry.val=val4 a+
          val4 (Array.make 4#usize [b[0]! &&& mask,b[1]! &&& mask,b[2]! &&& mask,b[3]! &&& mask]) ⦄ := by
  obtain ⟨a0,a1,a2,a3,ha⟩ : ∃ a0 a1 a2 a3 : U64,
      a=Array.make 4#usize [a0,a1,a2,a3] :=
    ⟨a[0]!,a[1]!,a[2]!,a[3]!,CommonVerify.array_four_eta a⟩
  obtain ⟨b0,b1,b2,b3,hb⟩ : ∃ b0 b1 b2 b3 : U64,
      b=Array.make 4#usize [b0,b1,b2,b3] :=
    ⟨b[0]!,b[1]!,b[2]!,b[3]!,CommonVerify.array_four_eta b⟩
  subst a b
  simpa [Array.to_slice] using half_loop_spec_four mask a0 a1 a2 a3 b0 b1 b2 b3

#print axioms half_loop_unfold
#print axioms half_loop_spec_four
#print axioms half_loop_spec
end UdonVerify.Native
