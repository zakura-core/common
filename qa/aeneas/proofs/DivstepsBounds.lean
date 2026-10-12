import DivstepsInteger
import Mathlib.Algebra.Order.Ring.Abs

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem integer_step_bound (state : State) (bound : Int) (hbound : 0 ≤ bound)
    (hodd : state.f % 2 = 1) (hf : |state.f| ≤ bound) (hg : |state.g| ≤ bound) :
    |(integerStep state).f| ≤ bound ∧ |(integerStep state).g| ≤ bound := by
  have hfRange := abs_le.mp hf
  have hgRange := abs_le.mp hg
  unfold integerStep chooseBranch
  split_ifs with heven hpositive
  · dsimp only
    refine ⟨hf, abs_le.mpr ?_⟩
    have hhalf := half_exact state.g heven
    constructor <;> omega
  · dsimp only
    have hgOdd : state.g % 2 = 1 := by omega
    refine ⟨hg, abs_le.mpr ?_⟩
    have hhalf := half_exact (state.g - state.f) (by omega)
    constructor <;> omega
  · dsimp only
    have hgOdd : state.g % 2 = 1 := by omega
    refine ⟨hf, abs_le.mpr ?_⟩
    have hhalf := half_exact (state.g + state.f) (by omega)
    constructor <;> omega

theorem integer_step_delta_bound (state : State) :
    |(integerStep state).delta| ≤ |state.delta| + 1 := by
  unfold integerStep chooseBranch
  split_ifs
  · simpa only [abs_one] using abs_add_le state.delta (1 : Int)
  · simpa only [abs_one, add_comm] using abs_sub (1 : Int) state.delta
  · simpa only [abs_one] using abs_add_le state.delta (1 : Int)

theorem iterate_bound (n : Nat) (state : State) (bound : Int) (hbound : 0 ≤ bound)
    (hodd : state.f % 2 = 1) (hf : |state.f| ≤ bound) (hg : |state.g| ≤ bound) :
    |(iterate n state).f| ≤ bound ∧ |(iterate n state).g| ≤ bound := by
  induction n with
  | zero => exact ⟨hf, hg⟩
  | succ n ih =>
      exact integer_step_bound _ bound hbound (iterate_odd n state hodd) ih.1 ih.2

theorem iterate_delta_bound (n : Nat) (state : State) :
    |(iterate n state).delta| ≤ |state.delta| + n := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      have h := integer_step_delta_bound (iterate n state)
      simp only [iterate, Nat.cast_succ]
      linarith only [h, ih]

theorem integer_step_doubled (state : State) (hodd : state.f % 2 = 1) :
    transform (chooseBranch state.delta state.g) ⟨state.f, state.g⟩ =
      ⟨2 * (integerStep state).f, 2 * (integerStep state).g⟩ := by
  unfold integerStep chooseBranch
  split_ifs with heven hpositive
  · exact congrArg (Vertex.mk (2 * state.f)) (half_exact state.g heven).symm
  · have hgOdd : state.g % 2 = 1 := by omega
    exact congrArg (Vertex.mk (2 * state.g)) (half_exact (state.g - state.f) (by omega)).symm
  · have hgOdd : state.g % 2 = 1 := by omega
    exact congrArg (Vertex.mk (2 * state.f)) (half_exact (state.g + state.f) (by omega)).symm

#print axioms iterate_bound
#print axioms iterate_delta_bound
#print axioms integer_step_doubled

end UdonVerify.SafeGcd
