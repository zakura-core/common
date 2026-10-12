import CommonFG62Value
import CommonDivstepFull

namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def coeffSignCorrection (value modulus : Int) : Int :=
  if value < 0 then value + modulus else value

def coeffCorrection (u v d e low mu : Int) : Int :=
  let initial := (if d < 0 then u else 0) + (if e < 0 then v else 0)
  initial - (mu * low + initial) % signedRadix

theorem coeff_sign_corrected_bound (value modulus : Int)
    (hm : 0 < modulus) (h : -2 * modulus < value ∧ value < modulus) :
    |coeffSignCorrection value modulus| < modulus := by
  unfold coeffSignCorrection
  split_ifs <;> rw [abs_lt] <;> omega

theorem coeff_correction_bound (u v d e low mu : Int)
    (hrow : |u| + |v| ≤ signedRadix) :
    -2 * signedRadix < coeffCorrection u v d e low mu ∧
      coeffCorrection u v d e low mu ≤ signedRadix := by
  have hu := abs_le.mp (show |u| ≤ signedRadix by have := abs_nonneg v; omega)
  have hv := abs_le.mp (show |v| ≤ signedRadix by have := abs_nonneg u; omega)
  have hsum := abs_add_le u v
  have htotal := abs_le.mp (show |u + v| ≤ signedRadix by omega)
  have hmod := row_digit_normalized (mu * low +
    ((if d < 0 then u else 0) + (if e < 0 then v else 0)))
  unfold coeffCorrection
  split_ifs at * <;> dsimp only at * <;> omega

theorem coeff_correction_cancels (u v d e low mu m0 : Int)
    (hmu : Int.ModEq signedRadix (m0 * mu) 1) :
    (low + m0 * coeffCorrection u v d e low mu) % signedRadix = 0 := by
  let initial := (if d < 0 then u else 0) + (if e < 0 then v else 0)
  have hresidue := Int.mod_modEq (mu * low + initial) signedRadix
  have hc : Int.ModEq signedRadix (coeffCorrection u v d e low mu) (-mu * low) := by
    have h := (Int.ModEq.refl initial).sub hresidue
    convert h using 1 <;> dsimp only [coeffCorrection, initial] <;> ring
  have hn := (Int.ModEq.refl low).add (hc.mul_left m0)
  have hm := hmu.mul_right low
  have hz : Int.ModEq signedRadix (low + m0 * coeffCorrection u v d e low mu) 0 := by
    calc
      _ ≡ low + m0 * (-mu * low) [ZMOD signedRadix] := hn
      _ = low - (m0 * mu) * low := by ring
      _ ≡ low - 1 * low [ZMOD signedRadix] := (Int.ModEq.refl low).sub hm
      _ = 0 := by ring
  exact hz

theorem coeff_row_numerator_bound (u v d e modulus low mu : Int)
    (hm : 0 < modulus) (hrow : |u| + |v| ≤ signedRadix)
    (hd : -2 * modulus < d ∧ d < modulus)
    (he : -2 * modulus < e ∧ e < modulus) :
    -2 * signedRadix * modulus < u * d + v * e + modulus * coeffCorrection u v d e low mu ∧
    u * d + v * e + modulus * coeffCorrection u v d e low mu < signedRadix * modulus := by
  have hdc := coeff_sign_corrected_bound d modulus hm hd
  have hec := coeff_sign_corrected_bound e modulus hm he
  have hprodD : |u * coeffSignCorrection d modulus| ≤ |u| * (modulus - 1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by omega) (abs_nonneg u)
  have hprodE : |v * coeffSignCorrection e modulus| ≤ |v| * (modulus - 1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by omega) (abs_nonneg v)
  have hs := abs_add_le (u * coeffSignCorrection d modulus) (v * coeffSignCorrection e modulus)
  have hweight := mul_le_mul_of_nonneg_right hrow (by omega : 0 ≤ modulus - 1)
  have hsum : |u * coeffSignCorrection d modulus + v * coeffSignCorrection e modulus| <
      signedRadix * modulus := by
    have hb : 0 < signedRadix := by norm_num [signedRadix]
    nlinarith
  have hbounds := abs_lt.mp hsum
  let initial := (if d < 0 then u else 0) + (if e < 0 then v else 0)
  have hres := row_digit_normalized (mu * low + initial)
  have hidentity : u * d + v * e + modulus * coeffCorrection u v d e low mu =
      u * coeffSignCorrection d modulus + v * coeffSignCorrection e modulus -
        modulus * ((mu * low + initial) % signedRadix) := by
    unfold coeffCorrection coeffSignCorrection initial
    split_ifs <;> ring
  rw [hidentity]
  have hproduct := mul_lt_mul_of_pos_left hres.2 hm
  have hnonneg := mul_nonneg (by omega : 0 ≤ modulus) hres.1
  constructor <;> nlinarith

theorem coeff_row_range (u v d e modulus low mu : Int)
    (hm : 0 < modulus) (hrow : |u| + |v| ≤ signedRadix)
    (hd : -2 * modulus < d ∧ d < modulus)
    (he : -2 * modulus < e ∧ e < modulus)
    (hdiv : signedRadix ∣ u * d + v * e + modulus * coeffCorrection u v d e low mu) :
    -2 * modulus < (u * d + v * e + modulus * coeffCorrection u v d e low mu) / signedRadix ∧
      (u * d + v * e + modulus * coeffCorrection u v d e low mu) / signedRadix < modulus := by
  have hb := coeff_row_numerator_bound u v d e modulus low mu hm hrow hd he
  have heq := Int.mul_ediv_cancel' hdiv
  have hr : 0 < signedRadix := by norm_num [signedRadix]
  constructor <;> nlinarith

#print axioms coeff_sign_corrected_bound
#print axioms coeff_correction_bound
#print axioms coeff_correction_cancels
#print axioms coeff_row_numerator_bound
#print axioms coeff_row_range
end UdonVerify.CommonSigned62
