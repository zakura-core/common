import NativeLargeCorrection

open Aeneas Std Result

namespace UdonVerify.LargeNativeBridge
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The four actual inverse lookups recover the complete inverse exponent. -/
@[step]
theorem large_recover_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (Native.kernelInst (nativeModulus inst))) (inverse root : Nat)
    (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1)
    (table : Native.LargeTable M) (multiplier : U32)
    (hchecks : Native.largeProgressionChecks (val4 params.modulus) inverse root table)
    (hlookup : Native.largeInverseChecks (val4 params.modulus) multiplier.val table)
    (hroot : (root : ZMod (val4 params.modulus)) ^ (256 ^ 4) = 1)
    (t : Element M Loose) (ht : looseValid (val4 params.modulus) t)
    (exponent : Nat) (hexponent : exponent < 256 ^ 4)
    (hcorrect : fieldValue (val4 params.modulus) inverse t *
      (root : ZMod (val4 params.modulus)) ^ exponent = 1) :
    largeRecover inst table t multiplier ⦃ out => out.val = exponent ⦄ := by
  let p := val4 params.modulus
  let d0 := exponent % 256
  let d1 := exponent / 256 % 256
  let d2 := exponent / 256 ^ 2 % 256
  let d3 := exponent / 256 ^ 3 % 256
  have hd0 : d0 < 256 := Nat.mod_lt _ (by decide)
  have hd1 : d1 < 256 := Nat.mod_lt _ (by decide)
  have hd2 : d2 < 256 := Nat.mod_lt _ (by decide)
  have hd3 : d3 < 256 := Nat.mod_lt _ (by decide)
  unfold largeRecover
  step -grind with (large_square_eight_spec inst params inverse hinverse t ht)
    as ⟨x2, hx2Bound, hx2Value⟩
  step -grind with (large_square_eight_spec inst params inverse hinverse x2 hx2Bound)
    as ⟨x1, hx1Bound, hx1Value⟩
  have hx1Pow : fieldValue p inverse x1 = fieldValue p inverse t ^ (256 ^ 2) := by
    rw [hx1Value, hx2Value, ← pow_mul]
    norm_num [p]
  step -grind with (large_square_eight_spec inst params inverse hinverse x1 hx1Bound)
    as ⟨x0, hx0Bound, hx0Value⟩
  have hx0Pow : fieldValue p inverse x0 = fieldValue p inverse t ^ (256 ^ 3) := by
    rw [hx0Value, hx1Pow, ← pow_mul]
    norm_num [p]
  have hc0 : fieldValue p inverse x0 * (root : ZMod p) ^ (d0 * 256 ^ 3) = 1 := by
    have h := LargeSqrt.corrected_lookup (root : ZMod p) (fieldValue p inverse t)
      exponent hroot hcorrect ⟨0, by decide⟩
    simpa [hx0Pow, d0, Nat.mod_one] using h
  step -grind with (large_inverse_lookup_spec inst params inverse root hinverse table multiplier
    hchecks hlookup hroot x0 hx0Bound d0 hd0 hc0) as ⟨e0, he0⟩
  simp only [lift, bind_ok]
  step -grind with (large_g2_entry_spec p inverse root table hchecks hinverse
    (UScalar.cast .Usize e0) (by simpa only [U32.cast_Usize_val_eq, he0] using hd0))
    as ⟨g20, hg20Bound, hg20Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse x1 g20 hx1Bound
    (by unfold looseValid reducedValid at *; omega)) as ⟨alpha0, ha0Bound, ha0Value⟩
  have ha0Pow : fieldValue p inverse alpha0 = fieldValue p inverse t ^ (256 ^ 2) *
      (root : ZMod p) ^ ((exponent % 256) * 256 ^ 2) := by
    simpa [p, hx1Value, hx2Value, ← pow_mul, hg20Value,
      U32.cast_Usize_val_eq, he0, d0] using ha0Value
  have hc1 : fieldValue p inverse alpha0 * (root : ZMod p) ^ (d1 * 256 ^ 3) = 1 := by
    have h := LargeSqrt.corrected_lookup (root : ZMod p) (fieldValue p inverse t)
      exponent hroot hcorrect ⟨1, by decide⟩
    simpa [ha0Pow, d1] using h
  step -grind with (large_inverse_lookup_spec inst params inverse root hinverse table multiplier
    hchecks hlookup hroot alpha0 ha0Bound d1 hd1 hc1) as ⟨e1, he1⟩
  step -grind with (large_append_spec e0 e1 8#i32 (by decide)
    (by simpa only [he0, show (2 : Nat) ^ (8#i32).val.toNat = 256 from by decide] using hd0)
    (by simpa only [he1] using hd1))
    as ⟨packed1, hp1Value, hp1Bound⟩
  have hp1 : packed1.val = exponent % 256 ^ 2 := by
    have h := LargeSqrt.digit_prefix exponent ⟨1, by decide⟩
    simp only [he0, he1, d0, d1] at hp1Value
    norm_num at hp1Value h ⊢
    omega
  step -grind with (large_low_index_spec packed1) as ⟨i10, hi10, hi10Bound⟩
  step -grind with (large_g1_entry_spec p inverse root table hchecks hinverse i10 hi10Bound)
    as ⟨g10, hg10Bound, hg10Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse x2 g10 hx2Bound
    (by unfold looseValid reducedValid at *; omega)) as ⟨a10, ha10Bound, ha10Value⟩
  step -grind with (large_top_index_spec packed1 8#i32 (by decide)) as ⟨i21, hi21⟩
  have hi21Bound : i21.val < 256 := by norm_num at hi21 hp1Bound ⊢; omega
  step -grind with (large_g2_entry_spec p inverse root table hchecks hinverse i21 hi21Bound)
    as ⟨g21, hg21Bound, hg21Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse a10 g21 ha10Bound
    (by unfold looseValid reducedValid at *; omega)) as ⟨alpha1, ha1Bound, ha1Value⟩
  have ha1Pow : fieldValue p inverse alpha1 = fieldValue p inverse t ^ 256 *
      (root : ZMod p) ^ ((exponent % 256 ^ 2) * 256) := by
    rw [ha1Value, ha10Value, hx2Value, hg10Value, hg21Value, mul_assoc, ← pow_add]
    congr 1
    congr 1
    have h := Nat.mod_add_div packed1.val 256
    rw [hi10, hi21, ← hp1]
    norm_num at h ⊢
    omega
  have hc2 : fieldValue p inverse alpha1 * (root : ZMod p) ^ (d2 * 256 ^ 3) = 1 := by
    have h := LargeSqrt.corrected_lookup (root : ZMod p) (fieldValue p inverse t)
      exponent hroot hcorrect ⟨2, by decide⟩
    simpa [ha1Pow, d2] using h
  step -grind with (large_inverse_lookup_spec inst params inverse root hinverse table multiplier
    hchecks hlookup hroot alpha1 ha1Bound d2 hd2 hc2) as ⟨e2, he2⟩
  step -grind with (large_append_spec packed1 e2 16#i32 (by decide)
    hp1Bound (by simpa only [he2] using hd2)) as ⟨packed2, hp2Value, hp2Bound⟩
  have hp2 : packed2.val = exponent % 256 ^ 3 := by
    have h := LargeSqrt.digit_prefix exponent ⟨2, by decide⟩
    simp only [hp1, he2, d2] at hp2Value
    norm_num at hp2Value h ⊢
    omega
  step -grind with (large_low_index_spec packed2) as ⟨i00, hi00, hi00Bound⟩
  step -grind with (large_g0_entry_spec p inverse root table hchecks hinverse i00 hi00Bound)
    as ⟨g00, hg00Bound, hg00Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse t g00 ht
    (by unfold looseValid reducedValid at *; omega)) as ⟨a00, ha00Bound, ha00Value⟩
  step -grind with (large_digit_index_spec packed2 8#i32 (by decide)) as ⟨i11, hi11, hi11Bound⟩
  step -grind with (large_g1_entry_spec p inverse root table hchecks hinverse i11 hi11Bound)
    as ⟨g11, hg11Bound, hg11Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse a00 g11 ha00Bound
    (by unfold looseValid reducedValid at *; omega)) as ⟨a11, ha11Bound, ha11Value⟩
  step -grind with (large_top_index_spec packed2 16#i32 (by decide)) as ⟨i22, hi22⟩
  have hi22Bound : i22.val < 256 := by norm_num at hi22 hp2Bound ⊢; omega
  step -grind with (large_g2_entry_spec p inverse root table hchecks hinverse i22 hi22Bound)
    as ⟨g22, hg22Bound, hg22Value⟩
  step -grind with (large_multiply_spec inst params inverse hinverse a11 g22 ha11Bound
    (by unfold looseValid reducedValid at *; omega)) as ⟨alpha2, ha2Bound, ha2Value⟩
  have ha2Pow : fieldValue p inverse alpha2 = fieldValue p inverse t *
      (root : ZMod p) ^ (exponent % 256 ^ 3) := by
    rw [ha2Value, ha11Value, ha00Value, hg00Value, hg11Value, hg22Value]
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    congr 1
    congr 1
    have h := LargeSqrt.four_bytes packed2.val (by norm_num at hp2Bound ⊢; omega)
    rw [hi00, hi11, hi22, ← hp2]
    norm_num at h hp2Bound ⊢
    omega
  have hc3 : fieldValue p inverse alpha2 * (root : ZMod p) ^ (d3 * 256 ^ 3) = 1 := by
    have h := LargeSqrt.corrected_lookup (root : ZMod p) (fieldValue p inverse t)
      exponent hroot hcorrect ⟨3, by decide⟩
    simpa [ha2Pow, d3] using h
  step -grind with (large_inverse_lookup_spec inst params inverse root hinverse table multiplier
    hchecks hlookup hroot alpha2 ha2Bound d3 hd3 hc3) as ⟨e3, he3⟩
  step -grind with (large_append_spec packed2 e3 24#i32 (by decide)
    hp2Bound (by simpa only [he3] using hd3)) as ⟨packed3, hp3Value, hp3Bound⟩
  try simp only [WP.spec_ok]
  have h := LargeSqrt.digit_prefix exponent ⟨3, by decide⟩
  simp only [hp2, he3, d3] at hp3Value
  norm_num at hp3Value h hexponent ⊢
  omega

#print axioms large_recover_spec

end UdonVerify.LargeNativeBridge
