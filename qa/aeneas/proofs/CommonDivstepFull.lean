import CommonDivstepBatch

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem divsteps_low_agreement (full low : State) (hfull : full.f % 2 = 1)
    (hlow : low.f % 2 = 1) (hmatch : LowMatches 62 full low) :
    transitionMatrix 62 full = transitionMatrix 62 low ∧
      (iterate 62 full).delta = (iterate 62 low).delta := by
  have hself : LowMatches 62 low low :=
    ⟨rfl, Int.ModEq.refl _, Int.ModEq.refl _⟩
  have hbranch (n : Nat) (hn : n < 62) :
      chooseBranch (iterate n full).delta (iterate n full).g =
        chooseBranch (iterate n low).delta (iterate n low).g := by
    exact (low_iterate_branch 62 n (by decide) hn full low hfull hmatch).symm.trans
      (low_iterate_branch 62 n (by decide) hn low low hlow hself)
  have hm (n : Nat) (hn : n ≤ 62) : transitionMatrix n full = transitionMatrix n low := by
    induction n with
    | zero => rfl
    | succ n ih => rw [transitionMatrix, transitionMatrix, ih (by omega), hbranch n (by omega)]
  have hf := low_iterate_matches 62 62 (by decide) (by decide) full low hfull hmatch
  have hl := low_iterate_matches 62 62 (by decide) (by decide) low low hlow hself
  exact ⟨hm 62 (by decide), hf.1.symm.trans hl.1⟩

@[step]
theorem native_divsteps_full_spec (eta : I64) (f0 g0 : U64) (f g : Int)
    (he : |eta.val| ≤ 683) (hf : f % 2 = 1)
    (hflow : Int.ModEq signedRadix (f0.val : Int) f)
    (hglow : Int.ModEq signedRadix (g0.val : Int) g) :
    CommonDivsteps.field.pasta.safegcd.divsteps_62_var eta f0 g0
      ⦃ out => NativeBatchResult ⟨-eta.val, f, g⟩ out ⦄ := by
  have hf0 := matched_word_odd 62 f0 f (by decide) hflow hf
  have hfull : LowMatches 62 ⟨-eta.val, f, g⟩ ⟨-eta.val, f0.val, g0.val⟩ :=
    ⟨rfl, hflow, hglow⟩
  have hf0int : (f0.val : Int) % 2 = 1 := by exact_mod_cast hf0
  obtain ⟨hm, hd⟩ := divsteps_low_agreement _ _ hf hf0int hfull
  apply WP.spec_mono (native_divsteps_spec eta f0 g0 he hf0)
  intro out h
  unfold NativeBatchResult at h ⊢
  simpa only [hm, hd] using h

theorem native_batch_transition (initial : State)
    (out : CommonDivsteps.field.pasta.safegcd.Trans2x2 × I64)
    (h : NativeBatchResult initial out) (hf : initial.f % 2 = 1) :
    out.1.u.val * initial.f + out.1.v.val * initial.g =
        signedRadix * (iterate 62 initial).f ∧
    out.1.q.val * initial.f + out.1.r.val * initial.g =
        signedRadix * (iterate 62 initial).g ∧
    out.1.u.val * out.1.r.val - out.1.v.val * out.1.q.val = signedRadix ∧
    |out.1.u.val| + |out.1.v.val| ≤ signedRadix ∧
    |out.1.q.val| + |out.1.r.val| ≤ signedRadix := by
  rcases h with ⟨hu, hv, hq, hr, _⟩
  rw [hu, hv, hq, hr]
  obtain ⟨hfirst, hsecond⟩ := transition_matrix_62 initial hf
  obtain ⟨hrowFirst, hrowSecond⟩ := transition_matrix_rows 62 initial
  exact ⟨hfirst, hsecond, transition_matrix_det 62 initial, hrowFirst, hrowSecond⟩

#print axioms divsteps_low_agreement
#print axioms native_divsteps_full_spec
#print axioms native_batch_transition
end UdonVerify.CommonSigned62
