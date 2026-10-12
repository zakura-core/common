import CommonFG62Digits
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def active62Value (limbs : Signed62) (len : Nat) : Int :=
  ∑ k ∈ Finset.range len, signedRadix ^ k * limbs[k]!.val

def fgRowInteger (u v : Int) (f g : Signed62) (k : Nat) : Int :=
  u * f[k]!.val + v * g[k]!.val

def fgCarry (term : Nat → Int) : Nat → Int
  | 0 => term 0 / signedRadix
  | k + 1 => (fgCarry term k + term (k + 1)) / signedRadix

def fgStoredDigit (term : Nat → Int) (len k : Nat) : Int :=
  if k + 1 < len then (fgCarry term k + term (k + 1)) % signedRadix
  else fgCarry term k

def fgRowMatches (len : Nat) (u v : Int) (f g before out : Signed62) : Prop :=
  ∀ k : Fin 5, out[k.val]!.val =
    if k.val < len then fgStoredDigit (fgRowInteger u v f g) len k.val
    else before[k.val]!.val

def fgInputsBounded (len : Nat) (f : Signed62) : Prop :=
  ∀ k : Fin 5, k.val < len → |f[k.val]!.val| ≤ signedRadix

theorem fg_matches_inactive (len : Nat) (u v : Int) (f g before out : Signed62)
    (h : fgRowMatches len u v f g before out) :
    ∀ k : Fin 5, len ≤ k.val → out[k.val]! = before[k.val]! := by
  intro k hk
  apply IScalar.eq_of_val_eq
  simpa only [if_neg (show ¬k.val < len by omega)] using h k

theorem fg_matches_normalized (len : Nat) (u v : Int) (f g before out : Signed62)
    (h : fgRowMatches len u v f g before out) :
    ∀ k : Fin 5, k.val + 1 < len →
      0 ≤ out[k.val]!.val ∧ out[k.val]!.val < signedRadix := by
  intro k hk
  have hd := h k
  rw [if_pos (show k.val < len by omega), fgStoredDigit, if_pos hk] at hd
  rw [hd]
  exact row_digit_normalized _

theorem fg_matches_value (len : Nat) (u v : Int) (f g before out : Signed62)
    (hlen : 1 ≤ len ∧ len ≤ 5)
    (hdiv : fgRowInteger u v f g 0 % signedRadix = 0)
    (h : fgRowMatches len u v f g before out) :
    signedRadix * active62Value out len =
      u * active62Value f len + v * active62Value g len := by
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  have h4 := h ⟨4, by decide⟩
  have hs0 := row_radix_split (fgRowInteger u v f g 0)
  have hs1 := row_radix_split (fgCarry (fgRowInteger u v f g) 0 + fgRowInteger u v f g 1)
  have hs2 := row_radix_split (fgCarry (fgRowInteger u v f g) 1 + fgRowInteger u v f g 2)
  have hs3 := row_radix_split (fgCarry (fgRowInteger u v f g) 2 + fgRowInteger u v f g 3)
  have hs4 := row_radix_split (fgCarry (fgRowInteger u v f g) 3 + fgRowInteger u v f g 4)
  obtain ⟨n, rfl⟩ : ∃ n : Fin 5, len = n.val + 1 :=
    ⟨⟨len - 1, by omega⟩, by dsimp; omega⟩
  fin_cases n <;>
    norm_num [fgStoredDigit, fgCarry, active62Value, Finset.sum_range_succ,
      fgRowInteger, signedRadix] at h0 h1 h2 h3 h4 hs0 hs1 hs2 hs3 hs4 hdiv ⊢ <;>
    ring_nf at h0 h1 h2 h3 h4 hs0 hs1 hs2 hs3 hs4 hdiv ⊢ <;> omega

#print axioms fg_matches_inactive
#print axioms fg_matches_normalized
#print axioms fg_matches_value
end UdonVerify.CommonSigned62
