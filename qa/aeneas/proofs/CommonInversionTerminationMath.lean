import CommonDivstepMatrix
import CommonSigned62Base

open UdonVerify.CommonSigned62
namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem first_matrix_second_row_nonzero (modulus x : Int) (t : Matrix)
    (hm : signedRadix < modulus) (hgcd : Int.gcd modulus x = 1)
    (hrow : |t.q| + |t.r| ≤ signedRadix)
    (hdet : t.u * t.r - t.v * t.q = signedRadix) :
    t.q * modulus + t.r * x ≠ 0 := by
  intro hzero
  have hb : 0 < signedRadix := by norm_num [signedRadix]
  have hm0 : 0 < modulus := by omega
  have hprod : modulus ∣ t.r * x := ⟨-t.q, by nlinarith only [hzero]⟩
  have hbez := Int.gcd_eq_gcd_ab modulus x
  rw [hgcd] at hbez
  norm_num only [Nat.cast_one] at hbez
  obtain ⟨k, hk⟩ := hprod
  have hdiv : modulus ∣ t.r := by
    refine ⟨t.r * Int.gcdA modulus x + k * Int.gcdB modulus x, ?_⟩
    calc
      t.r = t.r * 1 := by ring
      _ = t.r * (modulus * Int.gcdA modulus x + x * Int.gcdB modulus x) := by rw [← hbez]
      _ = modulus * (t.r * Int.gcdA modulus x) + (t.r * x) * Int.gcdB modulus x := by ring
      _ = modulus * (t.r * Int.gcdA modulus x + k * Int.gcdB modulus x) := by rw [hk]; ring
  have hr : |t.r| ≤ signedRadix := by have := abs_nonneg t.q; omega
  obtain ⟨j, hj⟩ := hdiv
  have hrzero : t.r = 0 := by
    by_contra hnonzero
    have hjnonzero : j ≠ 0 := by intro h; rw [h, mul_zero] at hj; exact hnonzero hj
    have hjabs : 1 ≤ |j| := by have := abs_pos.mpr hjnonzero; omega
    rw [hj, abs_mul, abs_of_pos hm0] at hr
    nlinarith only [hr, hm, hjabs, hm0]
  have hqzero : t.q = 0 := by
    rw [hrzero, zero_mul, add_zero] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hm0)
  rw [hrzero, hqzero, mul_zero, mul_zero, sub_self] at hdet
  omega

theorem first_batch_nonzero (modulus x : Int) (hm : signedRadix < modulus)
    (hodd : modulus % 2 = 1) (hgcd : Int.gcd modulus x = 1) :
    (iterate 62 ⟨1, modulus, x⟩).g ≠ 0 := by
  have htransition := (transition_matrix_62 ⟨1, modulus, x⟩ hodd).2
  have hrows := (transition_matrix_rows 62 ⟨1, modulus, x⟩).2
  have hdet := transition_matrix_det 62 ⟨1, modulus, x⟩
  have hnonzero := first_matrix_second_row_nonzero modulus x (transitionMatrix 62 ⟨1, modulus, x⟩) hm hgcd
    (by simpa only [signedRadix] using hrows) (by simpa only [signedRadix, matrixDet] using hdet)
  intro hzero
  apply hnonzero
  simpa only [hzero, mul_zero] using htransition

theorem inversion_terminal_unit (steps : Nat) (modulus x : Int)
    (hodd : modulus % 2 = 1) (hgcd : Int.gcd modulus x = 1)
    (hzero : (iterate steps ⟨1, modulus, x⟩).g = 0) :
    (iterate steps ⟨1, modulus, x⟩).f = 1 ∨ (iterate steps ⟨1, modulus, x⟩).f = -1 := by
  have h := iterate_gcd steps ⟨1, modulus, x⟩ hodd
  rw [hzero, hgcd] at h
  simp only [Int.gcd_zero_right] at h
  have habs : |(iterate steps ⟨1, modulus, x⟩).f| = 1 := by
    have hn := congrArg (fun n : Nat => (n : Int)) h
    simpa only [Int.natCast_natAbs, Nat.cast_one] using hn
  omega

#print axioms first_matrix_second_row_nonzero
#print axioms first_batch_nonzero
#print axioms inversion_terminal_unit
end UdonVerify.SafeGcd
