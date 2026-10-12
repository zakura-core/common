import CommonCoeffMath
import CommonFG62Sparse

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def coeffTerm (u v correction : Int) (d e modulus : Signed62) (k : Nat) : Int :=
  u * d[k]!.val + v * e[k]!.val + modulus[k]!.val * correction

def CoeffRowMatches (u v correction : Int) (d e modulus out : Signed62) : Prop :=
  ∀ k : Fin 5, out[k.val]!.val = fgStoredDigit (coeffTerm u v correction d e modulus) 5 k.val

theorem stored_row_value (term : Nat → Int) (out : Signed62)
    (hdiv : term 0 % signedRadix = 0)
    (h : ∀ k : Fin 5, out[k.val]!.val = fgStoredDigit term 5 k.val) :
    signedRadix * signed62Value out = term 0 + signedRadix * term 1 +
      signedRadix ^ 2 * term 2 + signedRadix ^ 3 * term 3 + signedRadix ^ 4 * term 4 := by
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  have h4 := h ⟨4, by decide⟩
  have hs0 := row_radix_split (term 0)
  have hs1 := row_radix_split (fgCarry term 0 + term 1)
  have hs2 := row_radix_split (fgCarry term 1 + term 2)
  have hs3 := row_radix_split (fgCarry term 2 + term 3)
  have hs4 := row_radix_split (fgCarry term 3 + term 4)
  norm_num [fgStoredDigit, fgCarry, signed62Value, signedRadix]
    at h0 h1 h2 h3 h4 hs0 hs1 hs2 hs3 hs4 hdiv ⊢
  ring_nf at h0 h1 h2 h3 h4 hs0 hs1 hs2 hs3 hs4 hdiv ⊢
  omega

theorem coeff_matches_value (u v correction : Int) (d e modulus out : Signed62)
    (hdiv : coeffTerm u v correction d e modulus 0 % signedRadix = 0)
    (h : CoeffRowMatches u v correction d e modulus out) :
    signedRadix * signed62Value out =
      u * signed62Value d + v * signed62Value e + signed62Value modulus * correction := by
  rw [stored_row_value (coeffTerm u v correction d e modulus) out hdiv h]
  unfold coeffTerm signed62Value
  ring

theorem coeff_matches_normalized (u v correction : Int) (d e modulus out : Signed62)
    (h : CoeffRowMatches u v correction d e modulus out) : signed62Normalized out := by
  intro k
  have hk : k.val < 5 := by have := k.isLt; omega
  have hv := h ⟨k.val, hk⟩
  dsimp only at hv
  rw [hv, fgStoredDigit, if_pos (by have := k.isLt; omega)]
  exact row_digit_normalized _

theorem coeff_matches_range (u v low mu : Int) (d e modulus out : Signed62)
    (hm : 0 < signed62Value modulus) (hrow : |u| + |v| ≤ signedRadix)
    (hd : -2 * signed62Value modulus < signed62Value d ∧ signed62Value d < signed62Value modulus)
    (he : -2 * signed62Value modulus < signed62Value e ∧ signed62Value e < signed62Value modulus)
    (hdiv : coeffTerm u v (coeffCorrection u v (signed62Value d) (signed62Value e) low mu)
      d e modulus 0 % signedRadix = 0)
    (h : CoeffRowMatches u v (coeffCorrection u v (signed62Value d) (signed62Value e) low mu)
      d e modulus out) :
    -2 * signed62Value modulus < signed62Value out ∧ signed62Value out < signed62Value modulus := by
  have hv := coeff_matches_value u v _ d e modulus out hdiv h
  have hb := coeff_row_numerator_bound u v (signed62Value d) (signed62Value e)
    (signed62Value modulus) low mu hm hrow hd he
  have hr : 0 < signedRadix := by norm_num [signedRadix]
  constructor <;> nlinarith

#print axioms stored_row_value
#print axioms coeff_matches_value
#print axioms coeff_matches_normalized
#print axioms coeff_matches_range
end UdonVerify.CommonSigned62
