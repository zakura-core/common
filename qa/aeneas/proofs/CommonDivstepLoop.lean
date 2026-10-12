import CommonDivstepLoopControl

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem native_odd_loop_induction (initial : State) (f0 g0 : U64)
    (hf0 : initial.f = (f0.val : Int)) (hg0 : initial.g = (g0.val : Int))
    (hiodd : initial.f % 2 = 1) (hi : |initial.delta| ≤ 683) (count : Nat) :
    ∀ (eta : I64) (u v q r f g : U64) (remaining : U32), remaining.val = count →
      (0 < remaining.val ∧ remaining.val ≤ 62) →
      BatchMatch initial eta u v q r f g remaining → g.val % 2 = 1 →
      nativeOddLoop f0 g0 eta u v q r f g remaining ⦃ out => BatchOutput initial out ⦄ := by
  induction count using Nat.strong_induction_on with
  | h count ih =>
    intro eta u v q r f g remaining hcount hr hmatch hgodd
    have he := batch_eta_bound initial eta u v q r f g remaining hi hmatch
    have hfodd := matched_word_odd (remaining.val + 2) f
      (iterate (62 - remaining.val) initial).f (by omega) hmatch.f_mod
      (iterate_odd (62 - remaining.val) initial hiodd)
    obtain ⟨hfirst, hsecond⟩ := batch_debug_rows initial f0 g0 eta u v q r f g remaining
      hf0 hg0 hiodd hr.2 hmatch
    unfold nativeOddLoop
    apply WP.spec_bind (native_odd_spec f0 g0 eta u v q r f g remaining
      he hr hfodd hgodd hfirst hsecond)
    intro flow hflow
    rcases hflow with ⟨cancel, hc, hflow⟩
    rcases cancel with ⟨nextEta, nextU, nextV, nextQ, nextR, nextF, nextG, mask, w⟩
    dsimp only at hflow
    rw [hflow]
    dsimp only
    rw [native_loop_head_bridge]
    have heNext : -745 ≤ nextEta.val ∧ nextEta.val ≤ 745 := by
      rcases hc with ⟨_, _, _, _, _, _, _, he0, he745, _⟩
      omega
    apply WP.spec_bind (strip_zero_state_spec nextEta nextU nextV
      (addMulWord nextG nextF w) remaining hr heNext)
    intro stripped hs
    rcases stripped with ⟨stripEta, stripU, stripV, stripG, rest, zeros⟩
    dsimp only at hs
    rcases hs with ⟨hz, hzbound, heta, hu, hv, hg, hrest, hzero, hstripOdd⟩
    obtain ⟨hz0, hadvance⟩ := native_cancel_advance
      (iterate (62 - remaining.val) initial) (transitionMatrix (62 - remaining.val) initial)
      eta u v q r f g remaining nextEta nextU nextV nextQ nextR nextF nextG mask w
      stripEta stripU stripV stripG zeros hr hmatch hfodd hgodd hc
      hz hzbound heta hu hv hg hzero
    have hbatch := batch_match_after_block initial stripEta stripU stripV
      (addMulWord nextQ nextU w) (addMulWord nextR nextV w) nextF stripG
      remaining rest zeros.val hr.2 hzbound hrest hadvance
    change (if rest = 0#u32 then
      ok (stripEta, stripU, stripV, addMulWord nextQ nextU w, addMulWord nextR nextV w)
      else nativeOddLoop f0 g0 stripEta stripU stripV (addMulWord nextQ nextU w)
        (addMulWord nextR nextV w) nextF stripG rest) ⦃ out => BatchOutput initial out ⦄
    split_ifs with hdone
    · simp only [WP.spec_ok]
      exact batch_output_of_done initial stripEta stripU stripV
        (addMulWord nextQ nextU w) (addMulWord nextR nextV w) nextF stripG
        rest (by rw [hdone]; rfl) hbatch
    · have hrest0 : 0 < rest.val := by scalar_tac
      exact ih rest.val (by omega) stripEta stripU stripV
        (addMulWord nextQ nextU w) (addMulWord nextR nextV w) nextF stripG rest
        rfl ⟨hrest0, by omega⟩ hbatch (hstripOdd hrest0)

@[step]
theorem native_loop_spec (initial : State) (f0 g0 : U64)
    (hf0 : initial.f = (f0.val : Int)) (hg0 : initial.g = (g0.val : Int))
    (hiodd : initial.f % 2 = 1) (hi : |initial.delta| ≤ 683)
    (eta : I64) (u v q r f g : U64) (remaining : U32)
    (hr : 0 < remaining.val ∧ remaining.val ≤ 62)
    (hmatch : BatchMatch initial eta u v q r f g remaining) :
    CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop eta f0 g0 u v q r f g remaining
      ⦃ out => BatchOutput initial out ⦄ := by
  rw [native_loop_head_bridge]
  have he := batch_eta_bound initial eta u v q r f g remaining hi hmatch
  apply WP.spec_bind (strip_zero_state_spec eta u v g remaining hr he)
  intro stripped hs
  rcases stripped with ⟨stripEta, stripU, stripV, stripG, rest, zeros⟩
  dsimp only at hs
  rcases hs with ⟨_, hzbound, heta, hu, hv, hg, hrest, hzero, hstripOdd⟩
  have hbatch := batch_even_advance initial eta stripEta u v q r f g stripU stripV stripG
    remaining rest zeros hr.2 hzbound hrest hmatch heta hu hv hg hzero
  change (if rest = 0#u32 then ok (stripEta, stripU, stripV, q, r)
    else nativeOddLoop f0 g0 stripEta stripU stripV q r f stripG rest)
      ⦃ out => BatchOutput initial out ⦄
  split_ifs with hdone
  · simp only [WP.spec_ok]
    exact batch_output_of_done initial stripEta stripU stripV q r f stripG
      rest (by rw [hdone]; rfl) hbatch
  · have hrest0 : 0 < rest.val := by scalar_tac
    exact native_odd_loop_induction initial f0 g0 hf0 hg0 hiodd hi rest.val
      stripEta stripU stripV q r f stripG rest rfl ⟨hrest0, by omega⟩
      hbatch (hstripOdd hrest0)

#print axioms native_odd_loop_induction
#print axioms native_loop_spec
end UdonVerify.CommonSigned62
