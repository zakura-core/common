import DivstepsCertificateCheck
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Ring.Divisibility.Basic

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

structure State where
  delta : Int
  f : Int
  g : Int
  deriving DecidableEq, Repr

def chooseBranch (delta g : Int) : Branch :=
  if g % 2 = 0 then .even else if 0 < delta then .swap else .add

def integerStep (state : State) : State :=
  match chooseBranch state.delta state.g with
  | .swap => ⟨1 - state.delta, state.g, (state.g - state.f) / 2⟩
  | .add => ⟨state.delta + 1, state.f, (state.g + state.f) / 2⟩
  | .even => ⟨state.delta + 1, state.f, state.g / 2⟩

def iterate : Nat → State → State
  | 0, state => state
  | n + 1, state => integerStep (iterate n state)

def scaledPoint (modulus scale : Int) (state : State) : Point :=
  ((state.f : ℚ) * scale / modulus, (state.g : ℚ) * scale / modulus)

theorem half_exact (value : Int) (heven : value % 2 = 0) : 2 * (value / 2) = value := by
  omega

theorem half_cast (value : Int) (heven : value % 2 = 0) :
    ((value / 2 : Int) : ℚ) = (value : ℚ) / 2 := by
  have h : (2 : ℚ) * ((value / 2 : Int) : ℚ) = (value : ℚ) := by
    exact_mod_cast half_exact value heven
  linarith

theorem integer_step_odd (state : State) (hodd : state.f % 2 = 1) :
    (integerStep state).f % 2 = 1 := by
  unfold integerStep chooseBranch
  split_ifs with heven hpositive
  · exact hodd
  · have hgOdd : state.g % 2 = 1 := by omega
    exact hgOdd
  · exact hodd

theorem integer_step_delta (state : State) :
    (integerStep state).delta = nextDelta state.delta (chooseBranch state.delta state.g) := by
  unfold integerStep
  cases chooseBranch state.delta state.g <;> rfl

theorem integer_step_scaled (modulus scale : Int) (state : State) (hodd : state.f % 2 = 1) :
    scaledPoint modulus (2 * scale) (integerStep state) =
      transformPoint (chooseBranch state.delta state.g) (scaledPoint modulus scale state) := by
  unfold integerStep chooseBranch
  split_ifs with heven hpositive
  · have hhalf := half_cast state.g heven
    apply Prod.ext <;> dsimp [scaledPoint, transformPoint]
    · push_cast
      ring
    · rw [hhalf]
      push_cast
      ring
  · have hgOdd : state.g % 2 = 1 := by omega
    have hhalf := half_cast (state.g - state.f) (by omega)
    apply Prod.ext <;> dsimp [scaledPoint, transformPoint]
    · push_cast
      ring
    · rw [hhalf]
      push_cast
      ring
  · have hgOdd : state.g % 2 = 1 := by omega
    have hhalf := half_cast (state.g + state.f) (by omega)
    apply Prod.ext <;> dsimp [scaledPoint, transformPoint]
    · push_cast
      ring
    · rw [hhalf]
      push_cast
      ring

theorem integer_step_zero (state : State) (hzero : state.g = 0) :
    (integerStep state).g = 0 := by
  simp [integerStep, chooseBranch, hzero]

theorem iterate_zero (n : Nat) (state : State) (hzero : state.g = 0) :
    (iterate n state).g = 0 := by
  induction n with
  | zero => exact hzero
  | succ n ih => exact integer_step_zero _ ih

theorem iterate_odd (n : Nat) (state : State) (hodd : state.f % 2 = 1) :
    (iterate n state).f % 2 = 1 := by
  induction n with
  | zero => exact hodd
  | succ n ih => exact integer_step_odd _ ih

theorem iterate_add (m n : Nat) (state : State) :
    iterate (m + n) state = iterate n (iterate m state) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change integerStep (iterate (m + n) state) = integerStep (iterate n (iterate m state))
      rw [ih]

theorem gcd_two_of_odd (f : Int) (hodd : f % 2 = 1) : Int.gcd f 2 = 1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hcf hcTwo
  have h := dvd_sub hcf (dvd_mul_of_dvd_left hcTwo (f / 2))
  have hvalue : f - 2 * (f / 2) = 1 := by omega
  simpa only [hvalue] using h

theorem gcd_half (f g : Int) (hodd : f % 2 = 1) (heven : g % 2 = 0) :
    Int.gcd f (g / 2) = Int.gcd f g := by
  have h := Int.gcd_mul_left_right_of_gcd_eq_one (n := f) (m := 2) (k := g / 2)
    (gcd_two_of_odd f hodd)
  rw [Int.mul_comm (g / 2) 2, half_exact g heven] at h
  exact h.symm

theorem integer_step_gcd (state : State) (hodd : state.f % 2 = 1) :
    Int.gcd (integerStep state).f (integerStep state).g = Int.gcd state.f state.g := by
  unfold integerStep chooseBranch
  split_ifs with heven hpositive
  · exact gcd_half state.f state.g hodd heven
  · have hgOdd : state.g % 2 = 1 := by omega
    rw [gcd_half state.g (state.g - state.f) hgOdd (by omega)]
    simp only [Int.gcd_self_sub_right, Int.gcd_comm]
  · have hgOdd : state.g % 2 = 1 := by omega
    rw [gcd_half state.f (state.g + state.f) hodd (by omega)]
    exact Int.gcd_add_self_right _ _

theorem iterate_gcd (n : Nat) (state : State) (hodd : state.f % 2 = 1) :
    Int.gcd (iterate n state).f (iterate n state).g = Int.gcd state.f state.g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate, integer_step_gcd _ (iterate_odd n state hodd), ih]

#print axioms integer_step_scaled
#print axioms integer_step_odd
#print axioms iterate_add
#print axioms iterate_gcd

end UdonVerify.SafeGcd
