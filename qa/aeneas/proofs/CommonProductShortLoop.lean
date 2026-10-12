import CommonProductShortSteps

open Aeneas Std Result
namespace UdonVerify.ProductShort
open UdonVerify.Products
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def SliceLoopInvariant {M S T : Type} (total : Nat) (state : PairIter M S T × A8) : Prop :=
  state.1.fst.slice.length = state.1.snd.slice.length ∧
  state.1.fst.i = state.1.snd.i ∧
  state.1.fst.i ≤ state.1.fst.slice.length ∧
  val8 state.2 + remaining state.1 = total

def sliceLoopMeasure {M S T : Type} (state : PairIter M S T × A8) : Nat :=
  state.1.fst.slice.length - state.1.fst.i

theorem slice_body_progress {M S T : Type} (total : Nat) (htotal : total < R ^ 2)
    (state : PairIter M S T × A8) (hinv : SliceLoopInvariant total state) :
    CommonProductShort.field.pasta.products.PastaField.sum_of_products_slice_loop.body state.1 state.2
      ⦃ flow => match flow with
        | .done out => val8 out = total
        | .cont next => SliceLoopInvariant total next ∧ sliceLoopMeasure next < sliceLoopMeasure state ⦄ := by
  rcases state with ⟨⟨⟨lhs,i⟩,⟨rhs,j⟩⟩,wide⟩
  rcases hinv with ⟨hlen,hij,hi,hvalue⟩
  dsimp only at hlen hij hi hvalue ⊢
  subst j
  by_cases ha : i < lhs.length
  · have hb : i < rhs.length := by omega
    have hstep := remaining_step lhs rhs i ha hb
    rw [hstep] at hvalue
    have hbound : val8 wide + val4 (lhs[i]'ha).limbs * val4 (rhs[i]'hb).limbs < R ^ 2 := by omega
    apply WP.spec_mono (slice_body_some_spec _ _ wide (lhs[i]'ha) (rhs[i]'hb)
      (pair_next_some_eq lhs rhs i ha hb) hbound)
    intro flow hflow
    rcases hflow with ⟨out,rfl,hout⟩
    constructor
    · dsimp only [SliceLoopInvariant]
      refine ⟨hlen,rfl,by omega,?_⟩
      omega
    · change lhs.length - (i+1) < lhs.length - i
      omega
  · have hindex : i = lhs.length := by omega
    have hremaining : remaining (⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ : PairIter M S T) = 0 := by
      simp [remaining, hindex, rawSum]
    rw [slice_body_eq]
    unfold sliceBody
    rw [pair_next_none_eq lhs rhs i (by omega)]
    simp only [bind_ok, Std.uncurry_apply_pair, WP.spec_ok]
    simpa only [hremaining, Nat.add_zero] using hvalue

@[step]
theorem slice_loop_spec {M S T : Type} (total : Nat) (iter : PairIter M S T) (wide : A8)
    (htotal : total < R ^ 2) (hinv : SliceLoopInvariant total (iter,wide)) :
    CommonProductShort.field.pasta.products.PastaField.sum_of_products_slice_loop iter wide
      ⦃ out => val8 out = total ⦄ := by
  unfold CommonProductShort.field.pasta.products.PastaField.sum_of_products_slice_loop
  apply loop.spec_decr_nat sliceLoopMeasure (SliceLoopInvariant total) (fun out => val8 out = total)
  · intro state hstate
    have hprogress := slice_body_progress total htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem slice_accumulation_spec {M S T : Type}
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length)
    (hbound : rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val < R ^ 2) :
    CommonProductShort.field.pasta.products.PastaField.sum_of_products_slice_loop
      ⟨⟨lhs,0⟩,⟨rhs,0⟩⟩ (Array.repeat 8#usize 0#u64)
      ⦃ out => val8 out = rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val ⦄ := by
  apply slice_loop_spec _ _ _ hbound
  dsimp only [SliceLoopInvariant]
  refine ⟨hlen,rfl,by omega,?_⟩
  simp [remaining, val8]

#print axioms slice_body_progress
#print axioms slice_loop_spec
#print axioms slice_accumulation_spec
end UdonVerify.ProductShort
