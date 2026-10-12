import CommonActiveZeroLoop

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem active_zero_slice_iff (a : Signed62) (len : Nat) (hlen : 1 ≤ len ∧ len ≤ 5) :
    (a[0]! = 0#i64 ∧ ∀ x ∈ a.val.slice 1 len, x = 0#i64) ↔
      ∀ k : Fin 5, k.val < len → a[k.val]!.val = 0 := by
  have hlength : a.val.length = 5 := a.property
  constructor
  · rintro ⟨h0, hs⟩ k hk
    by_cases hk0 : k.val = 0
    · simpa [hk0] using congrArg IScalar.val h0
    · have hindex : k.val - 1 < (a.val.slice 1 len).length := by
        rw [List.slice_length, hlength]
        omega
      have hmem : (a.val.slice 1 len)[k.val - 1]! ∈ a.val.slice 1 len := by
        apply List.mem_iff_getElem.mpr
        exact ⟨k.val - 1, hindex,
          (getElem!_pos (a.val.slice 1 len) (k.val - 1) hindex).symm⟩
      have hz := hs _ hmem
      have heq := List.getElem!_slice 1 len (k.val - 1) a.val
        ⟨by omega, by omega⟩
      have hkplus : 1 + (k.val - 1) = k.val := by omega
      rw [heq, hkplus] at hz
      simpa [Array.getElem!_Nat_eq] using congrArg IScalar.val hz
  · intro hall
    constructor
    · apply IScalar.eq_of_val_eq
      simpa using hall ⟨0, by decide⟩ (by dsimp; omega)
    · intro x hx
      obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hx
      have hsum : 1 + index < len := by
        rw [List.slice_length, hlength] at hindex
        omega
      rw [List.getElem_slice 1 len index a.val ⟨by omega, hsum⟩]
      apply IScalar.eq_of_val_eq
      have hz := hall ⟨1 + index, by omega⟩ hsum
      simpa [Array.getElem!_Nat_eq, getElem!_pos a.val (1 + index) (by omega)] using hz

@[step]
theorem active_zero_digits_spec (a : Signed62) (len : Usize) (hlen : 1 ≤ len.val ∧ len.val ≤ 5) :
    CommonInvHelpers.field.pasta.safegcd.is_zero a len ⦃ out =>
      out = true ↔ ∀ k : Fin 5, k.val < len.val → a[k.val]!.val = 0 ⦄ := by
  unfold CommonInvHelpers.field.pasta.safegcd.is_zero
  rw [fg_index_eq a 0#usize (by decide)]
  simp only [bind_ok]
  split_ifs with hfirst
  · simp only [WP.spec_ok]
    have hnonzero : a[0]!.val ≠ 0 := by scalar_tac
    constructor
    · intro h
      contradiction
    · intro hall
      exact (hnonzero (hall ⟨0, by decide⟩ (by dsimp; omega))).elim
  · have hfirstZero : a[0]! = 0#i64 := by
      apply IScalar.eq_of_val_eq
      scalar_tac
    step +scalarTac -grind with core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      as ⟨slice, hslice, _hlength⟩
    simp only [Array.val_to_slice] at hslice
    simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
    step -grind with (active_zero_loop_spec ⟨slice, 0⟩ 0#i64) as ⟨folded, hfolded⟩
    try simp only [WP.spec_ok]
    have hfold : folded = foldSignedOr slice.val 0#i64 := by
      simpa only [List.drop_zero] using hfolded
    have hz : folded = 0#i64 ↔ ∀ x ∈ a.val.slice 1 len.val, x = 0#i64 := by
      rw [hfold, fold_signed_or_zero]
      simp only [true_and, hslice]
    have hbit : decide (folded = 0#i64) = true ↔ folded = 0#i64 := by simp
    exact hbit.trans (hz.trans (by
      simpa only [hfirstZero, true_and] using active_zero_slice_iff a len.val hlen))

@[step]
theorem active_zero_spec (a : Signed62) (len : Usize) (hlen : 1 ≤ len.val ∧ len.val ≤ 5)
    (hn : active62Normalized a len.val) :
    CommonInvHelpers.field.pasta.safegcd.is_zero a len ⦃ out =>
      out = true ↔ active62Value a len.val = 0 ⦄ := by
  apply WP.spec_mono (active_zero_digits_spec a len hlen)
  intro out h
  exact h.trans (active62_zero_iff a len.val hlen hn).symm

#print axioms active_zero_slice_iff
#print axioms active_zero_digits_spec
#print axioms active_zero_spec
end UdonVerify.CommonSigned62
