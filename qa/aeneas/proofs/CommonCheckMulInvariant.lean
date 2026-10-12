import CommonCheckMulRound

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

structure CheckMulInvariant (a : Signed62) (alen : Usize) (factor : I64)
    (count : Nat) (carry : I128) (out : Signed62) : Prop where
  carry_bound : |carry.val| ≤ 3
  normalized : ∀ k : Fin 4, k.val < count →
    0 ≤ out[k.val]!.val ∧ out[k.val]!.val < signedRadix
  value : active62Value out count + signedRadix ^ count * carry.val =
    factor.val * active62Value a (min count alen.val)

theorem check_mul_invariant_initial (a : Signed62) (alen : Usize) (factor : I64) :
    CheckMulInvariant a alen factor 0 0#i128 (Array.repeat 5#usize 0#i64) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro k hk
    omega
  · simp [active62Value]

theorem check_mul_invariant_advance (a : Signed62) (alen : Usize) (factor : I64)
    (index : Usize) (carry nextCarry acc : I128) (out : Signed62)
    (hi : index.val < 4)
    (h : CheckMulInvariant a alen factor index.val carry out)
    (hacc : acc.val = carry.val +
      (if index.val < alen.val then a[index.val]!.val * factor.val else 0))
    (hcarry : nextCarry.val = acc.val / signedRadix) (hc : |nextCarry.val| ≤ 3) :
    CheckMulInvariant a alen factor (index.val + 1) nextCarry (out.set index (fgRowDigit acc)) := by
  have hdigit := fg_row_digit_value acc
  refine ⟨hc, ?_, ?_⟩
  · intro k hk
    by_cases heq : index.val = k.val
    · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨heq, by have := k.isLt; simpa using (show k.val < 5 by omega)⟩]
      exact hdigit.2
    · rw [Array.getElem!_Nat_set_ne _ _ _ _ heq]
      exact h.normalized k (by omega)
  · rw [active62_set_succ out index (fgRowDigit acc) (by omega), hcarry, hdigit.1, pow_succ]
    calc
      active62Value out index.val + signedRadix ^ index.val * (acc.val % signedRadix) +
          signedRadix ^ index.val * signedRadix * (acc.val / signedRadix) =
          active62Value out index.val + signedRadix ^ index.val * acc.val := by
        have hsplit := Int.emod_add_mul_ediv acc.val signedRadix
        calc
          _ = active62Value out index.val + signedRadix ^ index.val *
              (acc.val % signedRadix + signedRadix * (acc.val / signedRadix)) := by ring
          _ = _ := by rw [hsplit]
      _ = factor.val * active62Value a (min (index.val + 1) alen.val) := by
        rw [hacc, active62_min_succ]
        split_ifs <;> nlinarith only [h.value]

#print axioms check_mul_invariant_initial
#print axioms check_mul_invariant_advance
end UdonVerify.CommonSigned62
