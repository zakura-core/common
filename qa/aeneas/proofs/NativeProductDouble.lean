import NativeProductWords
import SquareProofs

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem double_with_bit (word carry : U64) (hcarry : carry.val ≤ 1) :
    ((word.val * 2) % B) ||| carry.val = (word.val * 2) % B + carry.val := by
  rw [double_low]
  exact (Nat.two_pow_add_eq_or_of_lt (i := 1) (by omega : carry.val < 2)
    (word.val % (2 ^ 63))).symm

open NativeField.zakura_udon.field.pasta.products.PastaField

theorem product_double_restore_eight (a0 a1 a2 a3 a4 a5 a6 a7 r0 r1 r2 r3 r4 r5 r6 r7 : U64) :
    Array.from_slice (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7])
      (((((((((Slice.from [a0,a1,a2,a3,a4,a5,a6,a7] (by scalar_tac)).setAtNat 7 r7).setAtNat 6 r6).setAtNat 5 r5).setAtNat 4 r4).setAtNat 3 r3).setAtNat 2 r2).setAtNat 1 r1).setAtNat 0 r0)
      = Array.make 8#usize [r0,r1,r2,r3,r4,r5,r6,r7] := by
  apply Aeneas.Std.Array.ext
  simp [Array.from_slice,Slice.setAtNat]

theorem product_double_loop_unfold (it : core.slice.iter.IterMut U64)
    (back : core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) (carry : U64) :
    product_difference_loop0 it back carry = (do
      let flow ← product_difference_loop0.body it back carry
      match flow with
      | .done out => ok out
      | .cont (it',back',carry') => product_difference_loop0 it' back' carry') := by
  unfold product_difference_loop0
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont state => rcases state with ⟨it',back',carry'⟩; rfl

@[step]
theorem product_double_loop_spec_eight (a0 a1 a2 a3 a4 a5 a6 a7 : U64) :
    product_difference_loop0 ⟨Slice.from [a0,a1,a2,a3,a4,a5,a6,a7] (by scalar_tac),0⟩ (fun it => it) 0#u64
      ⦃ carry it => carry.val ≤ 1 ∧
        val8 (Array.from_slice (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7]) it.slice)
          + R^2*carry.val = 2*val8 (Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7]) ⦄ := by
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry0, hnext0, hnextBound0⟩
  have hcarry0 : carry0.val ≤ 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hnext0
    norm_num at hnext0
    scalar_tac
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shift0, hshift0, hshiftBound0⟩
  let digit0 := shift0
  have hdigit0 : digit0.val=shift0.val := rfl
  have hjoin0 := double_with_bit a0 0#u64 (by decide)
  have hsplit0 := double_split a0
  try simp only [lift, bind_ok, Std.uncurry]
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry1, hnext1, hnextBound1⟩
  have hcarry1 : carry1.val ≤ 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hnext1
    norm_num at hnext1
    scalar_tac
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shift1, hshift1, hshiftBound1⟩
  step -grind with UScalar.or_spec as ⟨digit1, hdigit1, hdigitBound1⟩
  have hjoin1 := double_with_bit a1 carry0 hcarry0
  have hsplit1 := double_split a1
  try simp only [lift, bind_ok, Std.uncurry]
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry2, hnext2, hnextBound2⟩
  have hcarry2 : carry2.val ≤ 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hnext2
    norm_num at hnext2
    scalar_tac
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shift2, hshift2, hshiftBound2⟩
  step -grind with UScalar.or_spec as ⟨digit2, hdigit2, hdigitBound2⟩
  have hjoin2 := double_with_bit a2 carry1 hcarry1
  have hsplit2 := double_split a2
  try simp only [lift, bind_ok, Std.uncurry]
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry3, hnext3, hnextBound3⟩
  have hcarry3 : carry3.val ≤ 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hnext3
    norm_num at hnext3
    scalar_tac
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shift3, hshift3, hshiftBound3⟩
  step -grind with UScalar.or_spec as ⟨digit3, hdigit3, hdigitBound3⟩
  have hjoin3 := double_with_bit a3 carry2 hcarry2
  have hsplit3 := double_split a3
  try simp only [lift, bind_ok, Std.uncurry]
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry4, hnext4, hnextBound4⟩
  have hcarry4 : carry4.val ≤ 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hnext4
    norm_num at hnext4
    scalar_tac
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shift4, hshift4, hshiftBound4⟩
  step -grind with UScalar.or_spec as ⟨digit4, hdigit4, hdigitBound4⟩
  have hjoin4 := double_with_bit a4 carry3 hcarry3
  have hsplit4 := double_split a4
  try simp only [lift, bind_ok, Std.uncurry]
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry5, hnext5, hnextBound5⟩
  have hcarry5 : carry5.val ≤ 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hnext5
    norm_num at hnext5
    scalar_tac
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shift5, hshift5, hshiftBound5⟩
  step -grind with UScalar.or_spec as ⟨digit5, hdigit5, hdigitBound5⟩
  have hjoin5 := double_with_bit a5 carry4 hcarry4
  have hsplit5 := double_split a5
  try simp only [lift, bind_ok, Std.uncurry]
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry6, hnext6, hnextBound6⟩
  have hcarry6 : carry6.val ≤ 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hnext6
    norm_num at hnext6
    scalar_tac
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shift6, hshift6, hshiftBound6⟩
  step -grind with UScalar.or_spec as ⟨digit6, hdigit6, hdigitBound6⟩
  have hjoin6 := double_with_bit a6 carry5 hcarry5
  have hsplit6 := double_split a6
  try simp only [lift, bind_ok, Std.uncurry]
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, Std.bind_assoc]
  step -grind with U64.ShiftRight_IScalar_spec as ⟨carry7, hnext7, hnextBound7⟩
  have hcarry7 : carry7.val ≤ 1 := by
    simp only [Nat.shiftRight_eq_div_pow] at hnext7
    norm_num at hnext7
    scalar_tac
  step -grind with U64.ShiftLeft_IScalar_spec as ⟨shift7, hshift7, hshiftBound7⟩
  step -grind with UScalar.or_spec as ⟨digit7, hdigit7, hdigitBound7⟩
  have hjoin7 := double_with_bit a7 carry6 hcarry6
  have hsplit7 := double_split a7
  try simp only [lift, bind_ok, Std.uncurry]
  rw [product_double_loop_unfold]
  unfold product_difference_loop0.body
  simp [Slice.getElem_Nat_eq, core.slice.iter.IteratorIterMut.next, WP.spec_ok]
  rw [product_double_restore_eight]
  change carry7.val ≤ 1 ∧ shift0.val + B^1*digit1.val + B^2*digit2.val + B^3*digit3.val + B^4*digit4.val + B^5*digit5.val + B^6*digit6.val + B^7*digit7.val + R^2*carry7.val = 2*(a0.val + B^1*a1.val + B^2*a2.val + B^3*a3.val + B^4*a4.val + B^5*a5.val + B^6*a6.val + B^7*a7.val)
  refine ⟨hcarry7,?_⟩
  change carry0.val = a0.val >>> 63 at hnext0
  change shift0.val = (a0.val <<< 1) % U64.size at hshift0
  have ht0 : shift0.val=(a0.val*2)%B := by
    simpa [Nat.shiftLeft_eq,U64.size,U64.numBits,B] using hshift0
  simp only [Nat.shiftRight_eq_div_pow] at hnext0
  have hs0 : shift0.val+B*carry0.val=2*a0.val+0 := by
    rw [ht0,hnext0]
    nlinarith only [hsplit0]
  change carry1.val = a1.val >>> 63 at hnext1
  change shift1.val = (a1.val <<< 1) % U64.size at hshift1
  have ht1 : shift1.val=(a1.val*2)%B := by
    simpa [Nat.shiftLeft_eq,U64.size,U64.numBits,B] using hshift1
  simp only [Nat.shiftRight_eq_div_pow] at hnext1
  have hs1 : digit1.val+B*carry1.val=2*a1.val+carry0.val := by
    rw [hdigit1,UScalar.val_or,ht1,hnext1,hjoin1]
    nlinarith only [hsplit1]
  change carry2.val = a2.val >>> 63 at hnext2
  change shift2.val = (a2.val <<< 1) % U64.size at hshift2
  have ht2 : shift2.val=(a2.val*2)%B := by
    simpa [Nat.shiftLeft_eq,U64.size,U64.numBits,B] using hshift2
  simp only [Nat.shiftRight_eq_div_pow] at hnext2
  have hs2 : digit2.val+B*carry2.val=2*a2.val+carry1.val := by
    rw [hdigit2,UScalar.val_or,ht2,hnext2,hjoin2]
    nlinarith only [hsplit2]
  change carry3.val = a3.val >>> 63 at hnext3
  change shift3.val = (a3.val <<< 1) % U64.size at hshift3
  have ht3 : shift3.val=(a3.val*2)%B := by
    simpa [Nat.shiftLeft_eq,U64.size,U64.numBits,B] using hshift3
  simp only [Nat.shiftRight_eq_div_pow] at hnext3
  have hs3 : digit3.val+B*carry3.val=2*a3.val+carry2.val := by
    rw [hdigit3,UScalar.val_or,ht3,hnext3,hjoin3]
    nlinarith only [hsplit3]
  change carry4.val = a4.val >>> 63 at hnext4
  change shift4.val = (a4.val <<< 1) % U64.size at hshift4
  have ht4 : shift4.val=(a4.val*2)%B := by
    simpa [Nat.shiftLeft_eq,U64.size,U64.numBits,B] using hshift4
  simp only [Nat.shiftRight_eq_div_pow] at hnext4
  have hs4 : digit4.val+B*carry4.val=2*a4.val+carry3.val := by
    rw [hdigit4,UScalar.val_or,ht4,hnext4,hjoin4]
    nlinarith only [hsplit4]
  change carry5.val = a5.val >>> 63 at hnext5
  change shift5.val = (a5.val <<< 1) % U64.size at hshift5
  have ht5 : shift5.val=(a5.val*2)%B := by
    simpa [Nat.shiftLeft_eq,U64.size,U64.numBits,B] using hshift5
  simp only [Nat.shiftRight_eq_div_pow] at hnext5
  have hs5 : digit5.val+B*carry5.val=2*a5.val+carry4.val := by
    rw [hdigit5,UScalar.val_or,ht5,hnext5,hjoin5]
    nlinarith only [hsplit5]
  change carry6.val = a6.val >>> 63 at hnext6
  change shift6.val = (a6.val <<< 1) % U64.size at hshift6
  have ht6 : shift6.val=(a6.val*2)%B := by
    simpa [Nat.shiftLeft_eq,U64.size,U64.numBits,B] using hshift6
  simp only [Nat.shiftRight_eq_div_pow] at hnext6
  have hs6 : digit6.val+B*carry6.val=2*a6.val+carry5.val := by
    rw [hdigit6,UScalar.val_or,ht6,hnext6,hjoin6]
    nlinarith only [hsplit6]
  change carry7.val = a7.val >>> 63 at hnext7
  change shift7.val = (a7.val <<< 1) % U64.size at hshift7
  have ht7 : shift7.val=(a7.val*2)%B := by
    simpa [Nat.shiftLeft_eq,U64.size,U64.numBits,B] using hshift7
  simp only [Nat.shiftRight_eq_div_pow] at hnext7
  have hs7 : digit7.val+B*carry7.val=2*a7.val+carry6.val := by
    rw [hdigit7,UScalar.val_or,ht7,hnext7,hjoin7]
    nlinarith only [hsplit7]
  unfold R
  linear_combination hs0+B*hs1+B^2*hs2+B^3*hs3+B^4*hs4+B^5*hs5+B^6*hs6+B^7*hs7

@[step]
theorem product_double_loop_spec (product : A8) :
    product_difference_loop0 ⟨product.to_slice,0⟩ (fun it => it) 0#u64
      ⦃ carry it => carry.val ≤ 1 ∧
        val8 (Array.from_slice product it.slice)+R^2*carry.val = 2*val8 product ⦄ := by
  rw [array_eight_eta product]
  simpa [Array.to_slice] using product_double_loop_spec_eight
    product[0]! product[1]! product[2]! product[3]! product[4]! product[5]! product[6]! product[7]!

#print axioms double_with_bit
#print axioms product_double_restore_eight
#print axioms product_double_loop_unfold
#print axioms product_double_loop_spec_eight
#print axioms product_double_loop_spec
end UdonVerify.Native
