import Common

open Aeneas Std Result
open zakura_udon.field.pasta.word

namespace UdonVerify
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem double_low (a : Nat) : (a*2)%B = 2*(a%(2^63)) := by
  have h := Nat.mul_mod_mul_left 2 a (2^63)
  norm_num [B] at h ⊢
  simpa only [Nat.mul_comm a 2] using h

theorem double_split (a : U64) :
    (a.val*2)%B + B*(a.val/(2^63)) = 2*a.val := by
  rw [double_low]
  have h := Nat.mod_add_div a.val (2^63)
  norm_num [B] at h ⊢
  omega

theorem double_join (a b : U64) :
    ((a.val*2)%B) ||| (b.val/(2^63)) = (a.val*2)%B + b.val/(2^63) := by
  rw [double_low]
  have hb : b.val/(2^63) < 2 := by scalar_tac
  exact (Nat.two_pow_add_eq_or_of_lt (i := 1) hb (a.val%(2^63))).symm

@[step]
theorem square_wide_spec (value : A4) :
    square_wide value ⦃ out => val8 out = val4 value ^ 2 ⦄ := by
  unfold square_wide
  step with Array.index_usize_spec as ⟨ i, i_post ⟩
  step with Array.index_usize_spec as ⟨ i1, i1_post ⟩
  step with kernel_mac_identity as ⟨ r1, carry, r1_post ⟩
  step with Array.index_usize_spec as ⟨ i2, i2_post ⟩
  step with kernel_mac_identity as ⟨ r2, carry1, r2_post ⟩
  step with Array.index_usize_spec as ⟨ i3, i3_post ⟩
  step with kernel_mac_identity as ⟨ r3, r4, r3_post ⟩
  step with kernel_mac_identity as ⟨ r31, carry2, r31_post ⟩
  step with kernel_mac_identity as ⟨ r41, r5, r41_post ⟩
  step with kernel_mac_identity as ⟨ r51, r6, r51_post ⟩
  step with U64.ShiftRight_IScalar_spec as ⟨ r7, r7_post, r7_post1 ⟩
  step with U64.ShiftLeft_IScalar_spec as ⟨ i4, i4_post, i4_post1 ⟩
  step with U64.ShiftRight_IScalar_spec as ⟨ i5, i5_post, i5_post1 ⟩
  step with UScalar.or_spec as ⟨ r61, r61_post, r61_post1 ⟩
  step with U64.ShiftLeft_IScalar_spec as ⟨ i6, i6_post, i6_post1 ⟩
  step with U64.ShiftRight_IScalar_spec as ⟨ i7, i7_post, i7_post1 ⟩
  step with UScalar.or_spec as ⟨ r52, r52_post, r52_post1 ⟩
  step with U64.ShiftLeft_IScalar_spec as ⟨ i8, i8_post, i8_post1 ⟩
  step with U64.ShiftRight_IScalar_spec as ⟨ i9, i9_post, i9_post1 ⟩
  step with UScalar.or_spec as ⟨ r42, r42_post, r42_post1 ⟩
  step with U64.ShiftLeft_IScalar_spec as ⟨ i10, i10_post, i10_post1 ⟩
  step with U64.ShiftRight_IScalar_spec as ⟨ i11, i11_post, i11_post1 ⟩
  step with UScalar.or_spec as ⟨ r32, r32_post, r32_post1 ⟩
  step with U64.ShiftLeft_IScalar_spec as ⟨ i12, i12_post, i12_post1 ⟩
  step with U64.ShiftRight_IScalar_spec as ⟨ i13, i13_post, i13_post1 ⟩
  step with UScalar.or_spec as ⟨ r21, r21_post, r21_post1 ⟩
  step with U64.ShiftLeft_IScalar_spec as ⟨ r11, r11_post, r11_post1 ⟩
  step with kernel_mac_identity as ⟨ r0, carry3, r0_post ⟩
  step with kernel_adc_identity as ⟨ r12, carry4, r12_post ⟩
  step with kernel_mac_identity as ⟨ r22, carry5, r22_post ⟩
  step with kernel_adc_identity as ⟨ r33, carry6, r33_post ⟩
  step with kernel_mac_identity as ⟨ r43, carry7, r43_post ⟩
  step with kernel_adc_identity as ⟨ r53, carry8, r53_post ⟩
  step with kernel_mac_identity as ⟨ r62, carry9, r62_post ⟩
  step with kernel_adc_identity as ⟨ r71, carry10, r71_post ⟩

  have hd1 := double_split r1
  have hd2 := double_split r2
  have hd3 := double_split r31
  have hd4 := double_split r41
  have hd5 := double_split r51
  have hd6 := double_split r6
  have hj1 := double_join r2 r1
  have hj2 := double_join r31 r2
  have hj3 := double_join r41 r31
  have hj4 := double_join r51 r41
  have hj5 := double_join r6 r51
  have htotal :
      val8 (Array.make 8#usize [r0, r12, r22, r33, r43, r53, r62, r71]) +
        R^2 * carry10.val = val4 value ^ 2 := by
    simp_all [val4, val8, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      U64.size, U64.numBits]
    norm_num [B, R] at *
    simp_all only [hj1, hj2, hj3, hj4, hj5]
    ring_nf at *
    omega
  have hvlt := val4_lt value
  have hsquare : val4 value ^ 2 < R^2 := Nat.pow_lt_pow_left hvlt (by decide)
  have hcarry : carry10 = 0#u64 := by
    have hcval : carry10.val = 0 := by
      norm_num [B, R] at htotal hsquare
      omega
    scalar_tac
  step
  simpa [hcarry] using htotal

#print axioms square_wide_spec

end UdonVerify
