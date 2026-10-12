import CommonProductPortableMerge
import CommonProductPortableLanes

open Aeneas Std Result
namespace UdonVerify.ProductPortable
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev MergeIter (M : Type) := core.slice.iter.Iter (Sum M)

def mergeRemaining {M : Type} (iter : MergeIter M) : Nat :=
  ((iter.slice.val.drop iter.i).map sumInteger).sum

def MergeLoopInvariant {M : Type} (total : Nat) (state : MergeIter M × Sum M) : Prop :=
  state.1.i ≤ state.1.slice.length ∧ sumInteger state.2 + mergeRemaining state.1 = total

def mergeLoopMeasure {M : Type} (state : MergeIter M × Sum M) : Nat :=
  state.1.slice.length - state.1.i

theorem lane_list_sum {M : Type} (lanes : Lanes M) :
    (lanes.val.map sumInteger).sum = lanesInteger lanes := by
  rw [array_four_eta_generic lanes]
  simp [lanesInteger,Nat.add_assoc]

theorem merge_next_some_eq {M : Type} (slice : Aeneas.Std.Slice (Sum M)) (i : Nat) (hi : i < slice.length) :
    core.slice.iter.IteratorSliceIter.next (⟨slice,i⟩ : MergeIter M) =
      ok (some (slice[i]'hi),⟨slice,i+1⟩) := by
  simp [core.slice.iter.IteratorSliceIter.next, hi]
  rfl

theorem merge_remaining_step {M : Type} (slice : Aeneas.Std.Slice (Sum M)) (i : Nat) (hi : i < slice.length) :
    mergeRemaining (⟨slice,i⟩ : MergeIter M) = sumInteger (slice[i]'hi) +
      mergeRemaining (⟨slice,i+1⟩ : MergeIter M) := by
  unfold mergeRemaining
  dsimp only
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem merge_body_progress {M : Type} (inst : Modulus M) (total : Nat) (htotal : total < B ^ 9)
    (state : MergeIter M × Sum M) (hinv : MergeLoopInvariant total state) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4.body
      inst state.1 state.2 ⦃ flow => match flow with
        | .done out => sumInteger out = total
        | .cont next => MergeLoopInvariant total next ∧ mergeLoopMeasure next < mergeLoopMeasure state ⦄ := by
  rcases state with ⟨⟨slice,i⟩,sum⟩
  rcases hinv with ⟨hi,hvalue⟩
  dsimp only at hi hvalue ⊢
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4.body
  by_cases hnext : i < slice.length
  · have hstep := merge_remaining_step slice i hnext
    rw [hstep] at hvalue
    have hbound : sumInteger sum + sumInteger (slice[i]'hnext) < B ^ 9 := by omega
    rw [merge_next_some_eq slice i hnext]
    simp only [bind_ok,Std.uncurry_apply_pair]
    step -grind with (portable_merge_exact_spec inst sum (slice[i]'hnext) hbound) as ⟨out,hout⟩
    constructor
    · dsimp only [MergeLoopInvariant]
      exact ⟨by omega, by omega⟩
    · change slice.length - (i+1) < slice.length - i
      omega
  · have hindex : i = slice.length := by omega
    have hzero : mergeRemaining (⟨slice,i⟩ : MergeIter M) = 0 := by simp [mergeRemaining,hindex]
    simp [core.slice.iter.IteratorSliceIter.next, hnext, WP.spec_ok]
    simpa only [hzero,Nat.add_zero] using hvalue

@[step]
theorem merge_loop_spec {M : Type} (inst : Modulus M) (total : Nat) (iter : MergeIter M) (sum : Sum M)
    (htotal : total < B ^ 9) (hinv : MergeLoopInvariant total (iter,sum)) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4 inst iter sum
      ⦃ out => sumInteger out = total ⦄ := by
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4
  apply loop.spec_decr_nat mergeLoopMeasure (MergeLoopInvariant total) (fun out => sumInteger out = total)
  · intro state hstate
    have hprogress := merge_body_progress inst total htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem merge_accumulation_spec {M : Type} (inst : Modulus M) (slice : Aeneas.Std.Slice (Sum M)) (sum : Sum M)
    (hbound : sumInteger sum + (slice.val.map sumInteger).sum < B ^ 9) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop4 inst ⟨slice,0⟩ sum
      ⦃ out => sumInteger out = sumInteger sum + (slice.val.map sumInteger).sum ⦄ := by
  apply merge_loop_spec inst _ _ _ hbound
  dsimp only [MergeLoopInvariant]
  exact ⟨by omega,by simp [mergeRemaining]⟩

#print axioms lane_list_sum
#print axioms merge_next_some_eq
#print axioms merge_remaining_step
#print axioms merge_body_progress
#print axioms merge_loop_spec
#print axioms merge_accumulation_spec
end UdonVerify.ProductPortable
