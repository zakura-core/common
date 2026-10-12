import NativeIterator
import NativeBridge
open Aeneas Std Result
open NativeField.zakura_udon.field.pasta.encoding
namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
abbrev WideZip := core.iter.adapters.zip.Zip (core.slice.iter.IterMut U64)
  (core.array.iter.IntoIter U64 8#usize)

theorem wide_multiply_eq (lhs rhs : A4) :
    NativeField.zakura_udon.field.pasta.word.multiply_wide lhs rhs =
      udon_kernel_slice.field.pasta.word.multiply_wide lhs rhs := by rfl

theorem redc_unreduced_eq {M : Type} (inst : Modulus M) (limbs : A8) :
    NativeField.zakura_udon.field.pasta.montgomery.montgomery_reduce_unreduced inst limbs =
      udon_kernel_slice.field.pasta.montgomery.montgomery_reduce_unreduced (kernelInst inst) limbs := by rfl

theorem native_wide_adc_eq (lhs rhs carry : U64) :
    NativeField.zakura_udon.field.pasta.word.adc lhs rhs carry =
      udon_kernel_slice.field.pasta.word.adc lhs rhs carry := by rfl

theorem raw_add_loop_unfold (iter : WideZip) (back : WideZip → WideZip) (carry : U64) :
    raw_product_sum_loop iter back carry = (do
      let flow ← raw_product_sum_loop.body iter back carry
      match flow with
      | .done out => ok out
      | .cont (it,b,c) => raw_product_sum_loop it b c) := by
  unfold raw_product_sum_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont state => rcases state with ⟨it,b,c⟩; rfl

theorem list_eight_eta (values : List U64) (hlen : values.length=8) :
    values = [values[0]!,values[1]!,values[2]!,values[3]!,values[4]!,values[5]!,values[6]!,values[7]!] := by
  rcases values with _|⟨a0,values⟩
  · simp at hlen
  rcases values with _|⟨a1,values⟩
  · simp at hlen
  rcases values with _|⟨a2,values⟩
  · simp at hlen
  rcases values with _|⟨a3,values⟩
  · simp at hlen
  rcases values with _|⟨a4,values⟩
  · simp at hlen
  rcases values with _|⟨a5,values⟩
  · simp at hlen
  rcases values with _|⟨a6,values⟩
  · simp at hlen
  rcases values with _|⟨a7,values⟩
  · simp at hlen
  have hz : values=[] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_cons] at hlen
    omega
  subst values
  simp

theorem array_eight_eta (a : A8) :
    a = Array.make 8#usize [a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,a[7]!] := by
  apply Aeneas.Std.Array.ext
  simpa using list_eight_eta a.val (by simpa using a.property)

@[step]
theorem raw_add_loop_spec_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : U64) :
    raw_product_sum_loop ⟨⟨Slice.from [a0,a1,a2,a3,a4,a5,a6,a7] (by scalar_tac),0⟩,
      ⟨Slice.from [b0,b1,b2,b3,b4,b5,b6,b7] (by scalar_tac),0⟩⟩ (fun z => z) 0#u64
      ⦃ carry z => val8 (Array.from_slice (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7]) z.fst.slice)
        + R^2*carry.val = val8 (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])+val8 (Array.make 8#usize [b0,b1,b2,b3,b4,b5,b6,b7]) ⦄ := by
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair0,h0⟩
  rcases pair0 with ⟨r0,c0⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair1,h1⟩
  rcases pair1 with ⟨r1,c1⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair2,h2⟩
  rcases pair2 with ⟨r2,c2⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair3,h3⟩
  rcases pair3 with ⟨r3,c3⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair4,h4⟩
  rcases pair4 with ⟨r4,c4⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair5,h5⟩
  rcases pair5 with ⟨r5,c5⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair6,h6⟩
  rcases pair6 with ⟨r6,c6⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair7,h7⟩
  rcases pair7 with ⟨r7,c7⟩
  simp only [Std.uncurry_apply_pair, bind_ok]
  rw [raw_add_loop_unfold]
  unfold raw_product_sum_loop.body
  simp [mutableZipNext, core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorIterMut.next, core.slice.iter.IteratorSliceIter.next, WP.spec_ok]
  change r0.val+B*c0.val=a0.val+b0.val+0 at h0
  change r1.val+B*c1.val=a1.val+b1.val+c0.val at h1
  change r2.val+B*c2.val=a2.val+b2.val+c1.val at h2
  change r3.val+B*c3.val=a3.val+b3.val+c2.val at h3
  change r4.val+B*c4.val=a4.val+b4.val+c3.val at h4
  change r5.val+B*c5.val=a5.val+b5.val+c4.val at h5
  change r6.val+B*c6.val=a6.val+b6.val+c5.val at h6
  change r7.val+B*c7.val=a7.val+b7.val+c6.val at h7
  simp [val8, Array.from_slice, Slice.setAtNat]
  unfold R
  linear_combination h0+B^1*h1+B^2*h2+B^3*h3+B^4*h4+B^5*h5+B^6*h6+B^7*h7

@[step]
theorem raw_add_loop_spec (a b : A8) :
    raw_product_sum_loop ⟨⟨a.to_slice,0⟩,⟨b.to_slice,0⟩⟩ (fun z => z) 0#u64
      ⦃ carry z => val8 (Array.from_slice a z.fst.slice)+R^2*carry.val=val8 a+val8 b ⦄ := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,ha⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : U64,
      a=Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7] :=
    ⟨a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,a[5]!,a[6]!,a[7]!,array_eight_eta a⟩
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,hb⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 : U64,
      b=Array.make 8#usize [b0,b1,b2,b3,b4,b5,b6,b7] :=
    ⟨b[0]!,b[1]!,b[2]!,b[3]!,b[4]!,b[5]!,b[6]!,b[7]!,array_eight_eta b⟩
  subst a b
  simpa [Array.to_slice] using raw_add_loop_spec_eight a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7

#print axioms wide_multiply_eq
#print axioms redc_unreduced_eq
#print axioms native_wide_adc_eq
#print axioms raw_add_loop_unfold
#print axioms list_eight_eta
#print axioms array_eight_eta
#print axioms raw_add_loop_spec_eight
#print axioms raw_add_loop_spec
end UdonVerify.Native
