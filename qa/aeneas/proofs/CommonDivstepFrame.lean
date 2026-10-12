import CommonDivstepMatch

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

structure DivCancelFrame (original : State) (matrix : Matrix)
    (pre : State) (preMatrix : Matrix) : Prop where
  states : ∀ z, 0 < z → iterate z original = iterate z pre
  matrices : ∀ z, 0 < z → matrixMul (transitionMatrix z original) matrix =
    matrixMul (transitionMatrix z pre) preMatrix

theorem native_cancel_match (bits : Nat) (state : State) (matrix : Matrix)
    (eta : I64) (u v q r f g : U64) (remaining : U32)
    (nextEta : I64) (nextU nextV nextQ nextR nextF nextG mask w : U64)
    (hbits : 0 < bits ∧ bits ≤ 64)
    (h : DivWordMatch bits state matrix eta u v q r f g)
    (hfodd : f.val % 2 = 1) (hgodd : g.val % 2 = 1)
    (hc : NativeCancelRelation eta u v q r f g remaining
      (nextEta, nextU, nextV, nextQ, nextR, nextF, nextG, mask, w)) :
    ∃ n pre preMatrix,
      0 < n ∧ n ≤ remaining.val ∧ mask.val = 2 ^ n - 1 ∧ w.val < 2 ^ n ∧
      (nextG.val + nextF.val * w.val) % 2 ^ n = 0 ∧
      pre.delta + (n : Int) ≤ 1 ∧ pre.f % 2 = 1 ∧
      DivWordMatch bits pre preMatrix nextEta nextU nextV nextQ nextR nextF nextG ∧
      DivCancelFrame state matrix pre preMatrix := by
  rcases hc with ⟨n, hn0, hni, hne, hmask, hw, hcancel, he0, _, hcase⟩
  have hf := matched_integer_odd bits f state.f hbits.1 h.f_mod hfodd
  have hg := matched_integer_odd bits g state.g hbits.1 h.g_mod hgodd
  rcases hcase with hcase | hcase
  · rcases hcase with ⟨hneg, he, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hdelta : 0 < state.delta := by have := h.eta_value; omega
    refine ⟨n, swapPreState state, matrixMul rotationMatrix matrix,
      hn0, hni, hmask, hw, hcancel, ?_, hg, ?_, ?_⟩
    · have := h.eta_value
      dsimp only [swapPreState]
      omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [swapPreState]
        rw [he, h.eta_value]
      · simpa [matrixMul, rotationMatrix] using h.q_mod
      · simpa [matrixMul, rotationMatrix] using h.r_mod
      · simpa [matrixMul, rotationMatrix] using
          (wrapping_sub_mod_pow 0#u64 u 64 (by decide)).trans
            ((Int.ModEq.refl (0 : Int)).sub h.u_mod)
      · simpa [matrixMul, rotationMatrix] using
          (wrapping_sub_mod_pow 0#u64 v 64 (by decide)).trans
            ((Int.ModEq.refl (0 : Int)).sub h.v_mod)
      · exact h.g_mod
      · simpa [swapPreState] using
          (wrapping_sub_mod_pow 0#u64 f bits hbits.2).trans
            ((Int.ModEq.refl (0 : Int)).sub h.f_mod)
    · refine ⟨?_, ?_⟩
      · intro z hz
        exact swap_pre_iterate z state hz hdelta hf hg
      · intro z hz
        rw [swap_pre_matrix z state hz hdelta hf hg, matrix_mul_assoc]
  · rcases hcase with ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨n, state, matrix, hn0, hni, hmask, hw, hcancel, ?_, hf, h, ?_⟩
    · have := h.eta_value
      omega
    · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

#print axioms native_cancel_match
end UdonVerify.CommonSigned62
