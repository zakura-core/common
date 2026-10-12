import Mathlib.Tactic

namespace UdonVerify.Sqrt
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem predecessor_power (i : Nat) (hi : 0 < i) :
    (2 : Nat) ^ (i - 1) * 2 = 2 ^ i := by
  have h : i - 1 + 1 = i := by omega
  simpa only [h] using (pow_succ (2 : Nat) (i - 1)).symm

theorem half_power_minus_one {K : Type*} [Field K] (t : K) (i : Nat)
    (hi : 0 < i) (hpower : t ^ (2 ^ i) = 1)
    (hhalf : t ^ (2 ^ (i - 1)) ≠ 1) :
    t ^ (2 ^ (i - 1)) = -1 := by
  have hsquare : (t ^ (2 ^ (i - 1))) ^ 2 = 1 := by
    rw [← pow_mul, predecessor_power i hi]
    exact hpower
  exact (sq_eq_one_iff.mp hsquare).resolve_left hhalf

theorem correction_lowers_order {K : Type*} [Field K] (t root : K) (i : Nat)
    (hi : 0 < i) (hpower : t ^ (2 ^ i) = 1)
    (hhalf : t ^ (2 ^ (i - 1)) ≠ 1)
    (hroot : root ^ (2 ^ (i - 1)) = -1) :
    (t * root) ^ (2 ^ (i - 1)) = 1 := by
  rw [mul_pow, half_power_minus_one t i hi hpower hhalf, hroot]
  simp

theorem correction_preserves_square {K : Type*} [Field K] (x t a root nextRoot : K)
    (hinvariant : x ^ 2 = a * t) (hroot : nextRoot ^ 2 = root) :
    (x * nextRoot) ^ 2 = a * (t * root) := by
  rw [mul_pow, hinvariant, hroot]
  ring

theorem nonsquare_correction_preserves_square {K : Type*} [Field K] (x t a root : K)
    (hinvariant : x ^ 2 = a * t) :
    (x * root) ^ 2 = (a * root) * (t * root) := by
  rw [mul_pow, hinvariant]
  ring

/-- The maximal-order correction consumes the flag; other corrections lower m. -/
def correctionRank (m : Nat) (isSquare : Bool) : Nat :=
  m + if isSquare then 1 else 0

theorem correction_rank_decreases (m i : Nat) (isSquare : Bool) (hi : i < m) :
    correctionRank i isSquare < correctionRank m isSquare := by
  unfold correctionRank
  split <;> omega

theorem nonsquare_correction_rank_decreases (m : Nat) :
    correctionRank m false < correctionRank m true := by
  simp [correctionRank]

theorem nonsquare_of_alternate_root {K : Type*} [Field K] (a root x : K)
    (ha : a ≠ 0) (hroot : ¬ IsSquare root) (hx : x ^ 2 = a * root) :
    ¬ IsSquare a := by
  rintro ⟨y, hy⟩
  have hyNonzero : y ≠ 0 := by
    intro h
    subst y
    simp only [mul_zero] at hy
    exact ha hy
  apply hroot
  refine ⟨x / y, ?_⟩
  rw [div_mul_div_comm]
  apply (eq_div_iff (mul_ne_zero hyNonzero hyNonzero)).mpr
  calc
    root * (y * y) = a * root := by rw [← hy]; ring
    _ = x * x := by simpa only [pow_two] using hx.symm

theorem square_flag_correct {K : Type*} [Field K] (a root x : K) (flag : Bool)
    (ha : a ≠ 0) (hroot : ¬ IsSquare root)
    (hx : x ^ 2 = a * (if flag then 1 else root)) :
    flag = true ↔ IsSquare a := by
  cases flag
  · simp only [Bool.false_eq_true, ↓reduceIte, false_iff] at hx ⊢
    exact nonsquare_of_alternate_root a root x ha hroot hx
  · simp only [↓reduceIte, mul_one] at hx
    constructor
    · intro _
      exact ⟨x, by simpa only [pow_two] using hx.symm⟩
    · intro _; rfl

#print axioms correction_lowers_order
#print axioms correction_preserves_square
#print axioms nonsquare_correction_preserves_square
#print axioms square_flag_correct

end UdonVerify.Sqrt
