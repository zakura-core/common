import NativeLargeDigits

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The actual correction multiplies by the rounded half-exponent and reports its parity. -/
@[step]
theorem large_correct_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse root : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (table : Native.LargeTable M)
    (hchecks : Native.largeProgressionChecks (val4 params.modulus) inverse root table)
    (x : Element M Loose) (hx : looseValid (val4 params.modulus) x) (exponent : U32) :
    largeCorrect inst table x exponent ⦃ out =>
      out.1 = decide (exponent.val % 2 = 0) ∧
      looseValid (val4 params.modulus) out.2 ∧
      fieldValue (val4 params.modulus) inverse out.2 =
        fieldValue (val4 params.modulus) inverse x *
          (root : ZMod (val4 params.modulus)) ^ ((exponent.val + 1) / 2) ⦄ := by
  let p := val4 params.modulus
  unfold largeCorrect
  simp only [lift, bind_ok]
  step -grind with (Native.large_half_exponent_spec exponent) as ⟨half, hhalf, hhalfBound⟩
  step -grind with (large_low_index_spec half) as ⟨i0, hi0, hi0Bound⟩
  step -grind with (large_g0_entry_spec p inverse root table hchecks hinverse i0 hi0Bound)
    as ⟨g0, hg0Bound, hg0Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse x g0 hx
    (by unfold looseValid reducedValid at *; omega)) as ⟨x0, hx0Bound, hx0Value⟩
  step -grind with (large_digit_index_spec half 8#i32 (by decide)) as ⟨i1, hi1, hi1Bound⟩
  step -grind with (large_g1_entry_spec p inverse root table hchecks hinverse i1 hi1Bound)
    as ⟨g1, hg1Bound, hg1Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse x0 g1 hx0Bound
    (by unfold looseValid reducedValid at *; omega)) as ⟨x1, hx1Bound, hx1Value⟩
  step -grind with (large_digit_index_spec half 16#i32 (by decide)) as ⟨i2, hi2, hi2Bound⟩
  step -grind with (large_g2_entry_spec p inverse root table hchecks hinverse i2 hi2Bound)
    as ⟨g2, hg2Bound, hg2Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse x1 g2 hx1Bound
    (by unfold looseValid reducedValid at *; omega)) as ⟨x2, hx2Bound, hx2Value⟩
  step -grind with (large_top_index_spec half 24#i32 (by decide)) as ⟨i3, hi3⟩
  have hi3Bound : i3.val < 129 := by
    norm_num at hi3 hhalfBound ⊢
    omega
  step -grind with (large_g3_entry_spec p inverse root table hchecks hinverse i3 hi3Bound)
    as ⟨g3, hg3Bound, hg3Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse x2 g3 hx2Bound
    (by unfold looseValid reducedValid at *; omega)) as ⟨candidate, hcBound, hcValue⟩
  have hflag : (exponent &&& 1#u32 = 0#u32) ↔ exponent.val % 2 = 0 := by
    constructor
    · intro h
      have hv := congrArg (fun value : U32 => value.val) h
      simpa only [Native.large_mask_parity, show (0#u32).val = 0 from by decide] using hv
    · intro h
      apply UScalar.eq_of_val_eq
      simpa only [Native.large_mask_parity, show (0#u32).val = 0 from by decide] using h
  try simp only [WP.spec_ok]
  refine ⟨by simp only [hflag], hcBound, ?_⟩
  have hhalfSmall : half.val < 256 ^ 4 := by norm_num at hhalfBound ⊢; omega
  have hdigits := LargeSqrt.four_bytes half.val hhalfSmall
  have htop : half.val / 256 ^ 3 % 256 = half.val / 256 ^ 3 := by
    apply Nat.mod_eq_of_lt
    norm_num at hhalfBound ⊢
    omega
  rw [hcValue, hx2Value, hx1Value, hx0Value, hg0Value, hg1Value, hg2Value, hg3Value]
  simp only [hi0, hi1, hi2, hi3]
  norm_num only
  rw [mul_assoc, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  rw [← hhalf]
  congr 1
  norm_num at hdigits htop ⊢
  omega

#print axioms large_correct_spec

end UdonVerify.LargeNativeBridge
