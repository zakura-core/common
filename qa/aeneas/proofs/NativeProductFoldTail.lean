import NativeProductWords
open Aeneas Std Result
open NativeField.zakura_udon.field.pasta.products.ProductSum
namespace UdonVerify.Native
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
theorem fold_loop1_unfold (it : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) (carry : U64) :
    fold_overflow_loop0_loop0 it back carry = (do
      let r ← fold_overflow_loop0_loop0.body it back carry
      match r with
      | .done out => ok out
      | .cont (i,b,c) => fold_overflow_loop0_loop0 i b c) := by
  unfold fold_overflow_loop0_loop0
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨i,b,c⟩; rfl


theorem fold_splice_eight (a0 a1 a2 a3 a4 a5 a6 a7 r0 r1 r2 r3 : U64) :
    [a0,a1,a2,a3,a4,a5,a6,a7].setSlice! 1 [r0,r1,r2,r3] =
      [a0,r0,r1,r2,r3,a5,a6,a7] := by rfl

theorem slice_eight_drop_five (a0 a1 a2 a3 a4 a5 a6 a7 : U64) :
    (Slice.from [a0,a1,a2,a3,a4,a5,a6,a7] (by scalar_tac)).drop 5#usize =
      Slice.from [a5,a6,a7] (by scalar_tac) := by
  apply Slice.ext
  rfl

def val3 (s : Aeneas.Std.Slice U64) : Nat := s.val[0]!.val+B*s.val[1]!.val+B^2*s.val[2]!.val


theorem list_three_eta (values : List U64) (hlen : values.length=3) :
    values = [values[0]!,values[1]!,values[2]!] := by
  rcases values with _|⟨a0,values⟩
  · simp at hlen
  rcases values with _|⟨a1,values⟩
  · simp at hlen
  rcases values with _|⟨a2,values⟩
  · simp at hlen
  have hz : values=[] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_cons] at hlen
    omega
  subst values
  simp

theorem tail_splice_eight (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 : U64) :
    [a0,a1,a2,a3,a4,a5,a6,a7].setSlice! 5 [t0,t1,t2] =
      [a0,a1,a2,a3,a4,t0,t1,t2] := by rfl

theorem tail_splice_value (a0 a1 a2 a3 a4 a5 a6 a7 : U64)
    (tail : Aeneas.Std.Slice U64) (hlen : tail.val.length=3)
    (hsize : ([a0,a1,a2,a3,a4,a5,a6,a7].setSlice! 5 tail.val).length=8#usize.val) :
    val8 (Array.from ([a0,a1,a2,a3,a4,a5,a6,a7].setSlice! 5 tail.val) hsize) =
      a0.val+B*a1.val+B^2*a2.val+B^3*a3.val+B^4*a4.val+B^5*val3 tail := by
  have heta := list_three_eta tail.val hlen
  unfold val8 val3
  simp only [Array.getElem!_Nat_eq, Array.from_val]
  rw [heta]
  rw [tail_splice_eight]
  simp only [List.getElem!_cons_zero,List.getElem!_cons_succ]
  ring

@[step]
theorem fold_tail_spec (a b c initialCarry : U64) :
    fold_overflow_loop0_loop0 ⟨Slice.from [a,b,c] (by scalar_tac),0⟩ (fun it=>it) initialCarry
      ⦃ carry it back => carry.val≤1 ∧ (back it).slice.val.length=3 ∧
        val3 (back it).slice+B^3*carry.val=a.val+B*b.val+B^2*c.val+initialCarry.val ⦄ := by
  rw [fold_loop1_unfold]
  unfold fold_overflow_loop0_loop0.body
  simp [core.slice.iter.IteratorIterMut.next,Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair0,h0⟩
  rcases pair0 with ⟨r0,c0⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [fold_loop1_unfold]
  unfold fold_overflow_loop0_loop0.body
  simp [core.slice.iter.IteratorIterMut.next,Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair1,h1⟩
  rcases pair1 with ⟨r1,c1⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [fold_loop1_unfold]
  unfold fold_overflow_loop0_loop0.body
  simp [core.slice.iter.IteratorIterMut.next,Std.bind_assoc]
  rw [native_wide_adc_eq]
  step -grind with slice_adc_identity as ⟨pair2,h2⟩
  rcases pair2 with ⟨r2,c2⟩
  simp only [Std.uncurry_apply_pair,bind_ok]
  rw [fold_loop1_unfold]
  unfold fold_overflow_loop0_loop0.body
  simp [core.slice.iter.IteratorIterMut.next,Std.bind_assoc,WP.spec_ok]
  change r0.val+B*c0.val=a.val+0+initialCarry.val at h0
  have hc0 : c0.val≤1 := by
    norm_num only [B] at h0
    scalar_tac
  change r1.val+B*c1.val=b.val+0+c0.val at h1
  have hc1 : c1.val≤1 := adc_carry_le_one b 0#u64 c0 r1 c1 hc0 h1
  change r2.val+B*c2.val=c.val+0+c1.val at h2
  have hc2 : c2.val≤1 := adc_carry_le_one c 0#u64 c1 r2 c2 hc1 h2
  refine ⟨hc2,?_⟩
  simp [val3,Slice.setAtNat]
  linear_combination h0+B*h1+B^2*h2

#print axioms fold_tail_spec
end UdonVerify.Native
