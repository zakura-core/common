import DivstepsBounds

namespace UdonVerify.SafeGcd
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def InversionRanges (modulus : Int) (state : State) : Prop :=
  (-modulus < state.f ∧ state.f ≤ modulus) ∧ (-modulus < state.g ∧ state.g < modulus)

theorem integer_step_inversion_ranges (state : State) (modulus : Int) (hm : 0 < modulus)
    (hodd : state.f % 2 = 1) (hr : InversionRanges modulus state) :
    InversionRanges modulus (integerStep state) := by
  rcases hr with ⟨hf, hg⟩
  unfold InversionRanges integerStep chooseBranch
  split_ifs with heven hpositive
  · have hhalf := half_exact state.g heven
    dsimp only
    exact ⟨hf, by constructor <;> omega⟩
  · have hgOdd : state.g % 2 = 1 := by omega
    have hhalf := half_exact (state.g - state.f) (by omega)
    dsimp only
    exact ⟨⟨hg.1, le_of_lt hg.2⟩, by constructor <;> omega⟩
  · have hgOdd : state.g % 2 = 1 := by omega
    have hhalf := half_exact (state.g + state.f) (by omega)
    dsimp only
    exact ⟨hf, by constructor <;> omega⟩

theorem iterate_inversion_ranges (steps : Nat) (state : State) (modulus : Int)
    (hm : 0 < modulus) (hodd : state.f % 2 = 1) (hr : InversionRanges modulus state) :
    InversionRanges modulus (iterate steps state) := by
  induction steps with
  | zero => exact hr
  | succ n ih =>
    exact integer_step_inversion_ranges _ _ hm (iterate_odd n state hodd) ih

#print axioms integer_step_inversion_ranges
#print axioms iterate_inversion_ranges
end UdonVerify.SafeGcd
