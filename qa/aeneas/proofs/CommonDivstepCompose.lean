import CommonDivstepEven
import DivstepsLowBits

open UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem matrix_mul_assoc (a b c : Matrix) :
    matrixMul (matrixMul a b) c = matrixMul a (matrixMul b c) := by
  dsimp only [matrixMul]
  congr 1 <;> ring

theorem transition_matrix_add (m n : Nat) (state : State) :
    transitionMatrix (m + n) state =
      matrixMul (transitionMatrix n (iterate m state)) (transitionMatrix m state) := by
  induction n with
  | zero => simp [transitionMatrix, identityMatrix, matrixMul]
  | succ n ih =>
    rw [Nat.add_succ, transitionMatrix, transitionMatrix, ih, iterate_add, matrix_step_mul]

theorem no_swap_extended (n z : Nat) (state : State) (w : Int)
    (hnz : n ≤ z) (hdelta : state.delta + (n : Int) ≤ 1)
    (hodd : state.f % 2 = 1) (hw : 0 ≤ w ∧ w < 2 ^ n)
    (hdiv : (2 ^ z : Int) ∣ state.g + state.f * w) :
    iterate z state = ⟨state.delta + z, state.f, (state.g + state.f * w) / 2 ^ z⟩ ∧
      transitionMatrix z state = ⟨2 ^ z, 0, w, 1⟩ := by
  have hdivn : (2 ^ n : Int) ∣ state.g + state.f * w :=
    dvd_trans (pow_dvd_pow 2 hnz) hdiv
  have hm := no_swap_batch_matrix n state w hdelta hodd hw
    (Int.modEq_zero_iff_dvd.mpr hdivn)
  obtain ⟨hd, hf, _, _, _, _, _⟩ := no_swap_block n state hdelta
  have action := congrArg Vertex.y (transition_matrix_action n state hodd)
  rw [hm] at action
  dsimp only [matrixAction, scaleVertex] at action
  have hgNumerator : (2 : Int) ^ n * (iterate n state).g = state.g + state.f * w := by
    nlinarith only [action]
  have hg : (iterate n state).g = (state.g + state.f * w) / 2 ^ n := by
    rw [← hgNumerator, Int.mul_ediv_cancel_left _ (by positivity)]
  have hsum : n + (z - n) = z := by omega
  have hpow : (2 : Int) ^ n * 2 ^ (z - n) = 2 ^ z := by rw [← pow_add, hsum]
  have hpowReverse : (2 : Int) ^ (z - n) * 2 ^ n = 2 ^ z := by
    simpa only [mul_comm] using hpow
  obtain ⟨witness, hwitness⟩ := hdiv
  have htailDiv : (2 ^ (z - n) : Int) ∣ (iterate n state).g := by
    refine ⟨witness, ?_⟩
    apply mul_left_cancel₀ (show (2 : Int) ^ n ≠ 0 by positivity)
    calc
      (2 : Int) ^ n * (iterate n state).g = state.g + state.f * w := hgNumerator
      _ = 2 ^ z * witness := hwitness
      _ = 2 ^ n * (2 ^ (z - n) * witness) := by rw [← hpow]; ring
  obtain ⟨hstate, hmatrix⟩ := even_block (z - n) (iterate n state) htailDiv
  constructor
  · rw [← iterate_add, hsum, hd, hf, hg] at hstate
    have hp : ¬(2 ^ n : Int) < 0 :=
      not_lt_of_ge (show (0 : Int) ≤ 2 ^ n by positivity)
    simp only [Int.ediv_ediv, hp, false_and, if_false, sub_zero, hpow] at hstate
    have hdeltaSum : state.delta + (n : Int) + ((z - n : Nat) : Int) = state.delta + z := by omega
    simpa only [hdeltaSum] using hstate
  · have h := transition_matrix_add n (z - n) state
    rw [hsum, hmatrix, hm] at h
    simpa only [matrixMul, mul_zero, zero_mul, mul_one, one_mul, add_zero,
      zero_add, hpowReverse] using h

theorem swap_extended (n z : Nat) (state : State) (w : Int)
    (hz : 0 < z) (hnz : n ≤ z) (hdelta : 0 < state.delta)
    (hlimit : (n : Int) ≤ state.delta + 1)
    (hoddF : state.f % 2 = 1) (hoddG : state.g % 2 = 1)
    (hw : 0 ≤ w ∧ w < 2 ^ n)
    (hdiv : (2 ^ z : Int) ∣ -state.f + state.g * w) :
    iterate z state = ⟨-state.delta + z, state.g, (-state.f + state.g * w) / 2 ^ z⟩ ∧
      transitionMatrix z state = ⟨0, 2 ^ z, -1, w⟩ := by
  obtain ⟨hs, hm⟩ := no_swap_extended n z (swapPreState state) w hnz
    (by dsimp [swapPreState]; omega) hoddG hw hdiv
  constructor
  · rw [swap_pre_iterate z state hz hdelta hoddF hoddG, hs]
    rfl
  · rw [swap_pre_matrix z state hz hdelta hoddF hoddG, hm]
    simp [matrixMul, rotationMatrix]

#print axioms matrix_mul_assoc
#print axioms transition_matrix_add
#print axioms no_swap_extended
#print axioms swap_extended
end UdonVerify.CommonSigned62
