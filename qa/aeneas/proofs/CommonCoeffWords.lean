import CommonCoeffMath
import CommonDivstepWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem signed_cast_mod62 {ty : IScalarTy} (value : IScalar ty) :
    Int.ModEq signedRadix ((IScalar.hcast .U64 value).val : Int) value.val := by
  have hc : ((IScalar.hcast .U64 value).val : Int) = value.val % (2 ^ 64) := by
    rw [IScalar.hcast_val_eq]
    change ((value.val % (2 ^ 64)).toNat : Int) = value.val % (2 ^ 64)
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  rw [hc]
  exact (Int.mod_modEq value.val (2 ^ 64)).of_dvd (by norm_num [signedRadix])

def coeffResidue (mu : U64) (row : I128) (sign : I64) : U64 :=
  UScalar.wrapping_add (UScalar.wrapping_mul mu (IScalar.hcast .U64 row))
    (IScalar.hcast .U64 sign) &&& 4611686018427387903#u64

theorem coeff_residue_value (mu : U64) (row : I128) (sign : I64) :
    ((coeffResidue mu row sign).val : Int) = ((mu.val : Int) * row.val + sign.val) % signedRadix ∧
      (coeffResidue mu row sign).val < 2 ^ 62 := by
  let product := UScalar.wrapping_mul mu (IScalar.hcast .U64 row)
  let sum := UScalar.wrapping_add product (IScalar.hcast .U64 sign)
  have hp := (wrapping_mul_mod_pow mu (IScalar.hcast .U64 row) 62 (by decide)).trans
    ((signed_cast_mod62 row).mul_left (mu.val : Int))
  have hs := (wrapping_add_mod_pow product (IScalar.hcast .U64 sign) 62 (by decide)).trans
    (hp.add (signed_cast_mod62 sign))
  have hm : (coeffResidue mu row sign).val = sum.val % 2 ^ 62 :=
    and_mask_mod sum _ 62 mask62_value
  refine ⟨?_, ?_⟩
  · rw [hm, Int.natCast_emod]
    exact hs
  · rw [hm]
    exact Nat.mod_lt _ (by positivity)

def coeffResidueDigit (mu : U64) (row : I128) (sign : I64) : I64 :=
  UScalar.hcast .I64 (coeffResidue mu row sign)

theorem coeff_residue_digit_value (mu : U64) (row : I128) (sign : I64) :
    (coeffResidueDigit mu row sign).val = ((mu.val : Int) * row.val + sign.val) % signedRadix ∧
      0 ≤ (coeffResidueDigit mu row sign).val ∧ (coeffResidueDigit mu row sign).val < signedRadix := by
  obtain ⟨hv, hb⟩ := coeff_residue_value mu row sign
  have hcast := signed62_cast_value (coeffResidue mu row sign) hb
  have hrange := row_digit_normalized ((mu.val : Int) * row.val + sign.val)
  unfold coeffResidueDigit
  rw [hcast, hv]
  exact ⟨rfl, hrange⟩

def coeffCorrectWord (mu : U64) (row : I128) (sign : I64) : I64 :=
  IScalar.wrapping_sub sign (coeffResidueDigit mu row sign)

theorem coeff_correct_word_value (mu : U64) (row : I128) (sign : I64)
    (hs : |sign.val| ≤ signedRadix) :
    (coeffCorrectWord mu row sign).val =
      sign.val - ((mu.val : Int) * row.val + sign.val) % signedRadix ∧
      -2 * signedRadix < (coeffCorrectWord mu row sign).val ∧
      (coeffCorrectWord mu row sign).val ≤ signedRadix := by
  obtain ⟨hres, hres0, hres1⟩ := coeff_residue_digit_value mu row sign
  have hsRange := abs_le.mp hs
  have heq : (coeffCorrectWord mu row sign).val =
      sign.val - (coeffResidueDigit mu row sign).val := by
    unfold coeffCorrectWord
    rw [IScalar.wrapping_sub_val_eq]
    apply Arith.Int.bmod_pow2_eq_of_inBounds 63
    all_goals
      norm_num only [signedRadix] at hsRange hres0 hres1 ⊢
      omega
  refine ⟨by rw [heq, hres], ?_, ?_⟩
  · rw [heq]
    omega
  · rw [heq]
    omega

#print axioms signed_cast_mod62
#print axioms coeff_residue_value
#print axioms coeff_residue_digit_value
#print axioms coeff_correct_word_value
end UdonVerify.CommonSigned62
