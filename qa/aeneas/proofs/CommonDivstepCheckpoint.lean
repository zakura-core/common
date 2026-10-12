import CommonDivstepAdvance

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

abbrev BatchMatch (initial : State) (eta : I64) (u v q r f g : U64) (remaining : U32) :=
  DivWordMatch (remaining.val + 2) (iterate (62 - remaining.val) initial)
    (transitionMatrix (62 - remaining.val) initial) eta u v q r f g

def BatchOutput (initial : State) (out : DivWordOutput) : Prop :=
  out.1.val = -(iterate 62 initial).delta ∧
  Int.ModEq (2 ^ 64) (out.2.1.val : Int) (transitionMatrix 62 initial).u ∧
  Int.ModEq (2 ^ 64) (out.2.2.1.val : Int) (transitionMatrix 62 initial).v ∧
  Int.ModEq (2 ^ 64) (out.2.2.2.1.val : Int) (transitionMatrix 62 initial).q ∧
  Int.ModEq (2 ^ 64) (out.2.2.2.2.val : Int) (transitionMatrix 62 initial).r

theorem batch_match_initial (eta : I64) (f0 g0 : U64) :
    BatchMatch ⟨-eta.val, f0.val, g0.val⟩ eta 1#u64 0#u64 0#u64 1#u64 f0 g0 62#u32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [iterate, transitionMatrix, identityMatrix]

theorem batch_eta_bound (initial : State) (eta : I64) (u v q r f g : U64) (remaining : U32)
    (hi : |initial.delta| ≤ 683) (h : BatchMatch initial eta u v q r f g remaining) :
    -745 ≤ eta.val ∧ eta.val ≤ 745 := by
  have hb := iterate_delta_bound (62 - remaining.val) initial
  have hv := h.eta_value
  have habs := abs_le.mp hb
  omega

theorem batch_match_after_block (initial : State) (eta : I64) (u v q r f g : U64)
    (remaining rest : U32) (z : Nat) (hr : remaining.val ≤ 62) (hz : z ≤ remaining.val)
    (hrest : rest.val = remaining.val - z)
    (h : DivWordMatch (remaining.val + 2 - z)
      (iterate z (iterate (62 - remaining.val) initial))
      (matrixMul (transitionMatrix z (iterate (62 - remaining.val) initial))
        (transitionMatrix (62 - remaining.val) initial)) eta u v q r f g) :
    BatchMatch initial eta u v q r f g rest := by
  rw [← iterate_add, ← transition_matrix_add] at h
  have htime : 62 - remaining.val + z = 62 - rest.val := by omega
  have hbits : remaining.val + 2 - z = rest.val + 2 := by omega
  rwa [htime, hbits] at h

theorem batch_even_advance (initial : State)
    (eta nextEta : I64) (u v q r f g nextU nextV nextG : U64) (remaining rest zeros : U32)
    (hr : remaining.val ≤ 62) (hz : zeros.val ≤ remaining.val)
    (hrest : rest.val = remaining.val - zeros.val)
    (h : BatchMatch initial eta u v q r f g remaining)
    (heta : nextEta.val = eta.val - (zeros.val : Int))
    (hu : nextU.bv = u.bv <<< zeros.val) (hv : nextV.bv = v.bv <<< zeros.val)
    (hg : nextG.val = g.val / 2 ^ zeros.val) (hzero : g.val % 2 ^ zeros.val = 0) :
    BatchMatch initial nextEta nextU nextV q r f nextG rest := by
  obtain ⟨hdiv, hshift⟩ := matched_shift (remaining.val + 2) zeros.val
    (iterate (62 - remaining.val) initial) (transitionMatrix (62 - remaining.val) initial)
    eta nextEta u v q r f g nextU nextV nextG (by omega) (by omega) h heta hu hv hg hzero
  obtain ⟨hs, hm⟩ := even_block zeros.val (iterate (62 - remaining.val) initial) hdiv
  apply batch_match_after_block initial nextEta nextU nextV q r f nextG
    remaining rest zeros.val hr hz hrest
  rwa [hs, hm]

theorem batch_output_of_done (initial : State) (eta : I64) (u v q r f g : U64)
    (remaining : U32) (hr : remaining.val = 0)
    (h : BatchMatch initial eta u v q r f g remaining) :
    BatchOutput initial (eta, u, v, q, r) := by
  have ht : 62 - remaining.val = 62 := by omega
  exact ⟨by simpa only [ht] using h.eta_value,
    by simpa only [ht] using h.u_mod,
    by simpa only [ht] using h.v_mod,
    by simpa only [ht] using h.q_mod,
    by simpa only [ht] using h.r_mod⟩

theorem batch_debug_rows (initial : State) (f0 g0 : U64)
    (eta : I64) (u v q r f g : U64) (remaining : U32)
    (hf0 : initial.f = (f0.val : Int)) (hg0 : initial.g = (g0.val : Int))
    (hiodd : initial.f % 2 = 1) (hr : remaining.val ≤ 62)
    (h : BatchMatch initial eta u v q r f g remaining) :
    (rowWord u v f0 g0).bv = f.bv <<< (62 - remaining.val) ∧
    (rowWord q r f0 g0).bv = g.bv <<< (62 - remaining.val) := by
  have haction := transition_matrix_action (62 - remaining.val) initial hiodd
  have hfirst := congrArg Vertex.x haction
  have hsecond := congrArg Vertex.y haction
  dsimp only [matrixAction, scaleVertex] at hfirst hsecond
  rw [hf0, hg0] at hfirst hsecond
  have hbits : 64 - (62 - remaining.val) = remaining.val + 2 := by omega
  constructor
  · have heq := row_word_shift_eq u v f0 g0 f ⟨f.bv <<< (62 - remaining.val)⟩
      _ _ _ (62 - remaining.val) (by omega) h.u_mod h.v_mod
      (by simpa only [hbits] using h.f_mod) hfirst rfl
    exact congrArg UScalar.bv heq
  · have heq := row_word_shift_eq q r f0 g0 g ⟨g.bv <<< (62 - remaining.val)⟩
      _ _ _ (62 - remaining.val) (by omega) h.q_mod h.r_mod
      (by simpa only [hbits] using h.g_mod) hsecond rfl
    exact congrArg UScalar.bv heq

#print axioms batch_match_initial
#print axioms batch_eta_bound
#print axioms batch_match_after_block
#print axioms batch_even_advance
#print axioms batch_output_of_done
#print axioms batch_debug_rows
end UdonVerify.CommonSigned62
