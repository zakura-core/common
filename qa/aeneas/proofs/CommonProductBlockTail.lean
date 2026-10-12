import CommonProductBlockQuad

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def tailRemaining {M S T : Type} (li ri : Usize) (it : PairIter M S T) : Nat :=
  wordDot (fun a => a.limbs) (fun b => b.limbs) li.val ri.val
    (it.fst.slice.val.drop it.fst.i) (it.snd.slice.val.drop it.snd.i)

def TailInvariant {M S T : Type} (li ri : Usize) (total : Nat)
    (state : PairIter M S T × BatchColumns) : Prop :=
  state.1.fst.slice.length = state.1.snd.slice.length ∧
    state.1.fst.i = state.1.snd.i ∧ state.1.fst.i ≤ state.1.fst.slice.length ∧
    batchColumnsInteger state.2 + tailRemaining li ri state.1 = total

def tailMeasure {M S T : Type} (state : PairIter M S T × BatchColumns) : Nat :=
  state.1.fst.slice.length - state.1.fst.i

theorem tail_remaining_step {M S T : Type} (li ri : Usize)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (i : Nat) (ha : i < lhs.length) (hb : i < rhs.length) :
    tailRemaining li ri (⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ : PairIter M S T) =
      (lhs[i]'ha).limbs[li.val]!.val * (rhs[i]'hb).limbs[ri.val]!.val +
        tailRemaining li ri (⟨⟨lhs,i+1⟩,⟨rhs,i+1⟩⟩ : PairIter M S T) := by
  unfold tailRemaining wordDot
  dsimp only
  rw [List.drop_eq_getElem_cons ha,List.drop_eq_getElem_cons hb]
  rfl

theorem tail_body_progress {M S T : Type} (li ri : Usize) (hi : li.val < 4) (hj : ri.val < 4)
    (total : Nat) (htotal : total < B ^ 3) (state : PairIter M S T × BatchColumns)
    (hinv : TailInvariant li ri total state) :
    tailBody li ri state.1 state.2 ⦃ flow => match flow with
      | .done out => batchColumnsInteger out = total
      | .cont next => TailInvariant li ri total next ∧ tailMeasure next < tailMeasure state ⦄ := by
  rcases state with ⟨⟨⟨lhs,i⟩,⟨rhs,j⟩⟩,columns⟩
  rcases hinv with ⟨hlen,hij,hidx,hvalue⟩
  dsimp only at hlen hij hidx hvalue ⊢
  subst j
  by_cases ha : i < lhs.length
  · have hb : i < rhs.length := by omega
    have hstep := tail_remaining_step li ri lhs rhs i ha hb
    rw [hstep] at hvalue
    rw [tail_body_some_eq li ri _ _ columns _ _ (slice_pair_next_some lhs rhs i ha hb)]
    step -grind with (add_at_spec 0#usize li ri columns (lhs[i]'ha) (rhs[i]'hb) (by decide) hi hj (by omega))
      as ⟨out,hout⟩
    constructor
    · dsimp only [TailInvariant]
      exact ⟨hlen,rfl,by omega,by omega⟩
    · change lhs.length - (i+1) < lhs.length - i
      omega
  · unfold tailBody
    rw [slice_pair_next_none lhs rhs i (by omega)]
    simp only [bind_ok,Std.uncurry_apply_pair,WP.spec_ok]
    have hrem : tailRemaining li ri (⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ : PairIter M S T) = 0 := by
      simp [tailRemaining, show i = lhs.length from by omega, wordDot,rawSum]
    omega

@[step]
theorem tail_loop_spec {M S T : Type} (li ri : Usize) (hi : li.val < 4) (hj : ri.val < 4)
    (total : Nat) (iter : PairIter M S T) (columns : BatchColumns) (htotal : total < B ^ 3)
    (hinv : TailInvariant li ri total (iter,columns)) :
    tailLoop li ri iter columns ⦃ out => batchColumnsInteger out = total ⦄ := by
  unfold tailLoop
  apply loop.spec_decr_nat tailMeasure (TailInvariant li ri total) (fun out => batchColumnsInteger out = total)
  · intro state hstate
    have hprogress := tail_body_progress li ri hi hj total htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem tail_accumulation_spec {M S T : Type} (li ri : Usize) (hi : li.val < 4) (hj : ri.val < 4)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) (columns : BatchColumns)
    (hlen : lhs.length = rhs.length)
    (hbound : batchColumnsInteger columns + wordDot (fun a => a.limbs) (fun b => b.limbs)
      li.val ri.val lhs.val rhs.val < B ^ 3) :
    tailLoop li ri ⟨⟨lhs,0⟩,⟨rhs,0⟩⟩ columns ⦃ out =>
      batchColumnsInteger out = batchColumnsInteger columns + wordDot
        (fun a => a.limbs) (fun b => b.limbs) li.val ri.val lhs.val rhs.val ⦄ := by
  apply tail_loop_spec li ri hi hj _ _ _ hbound
  dsimp only [TailInvariant]
  refine ⟨hlen,rfl,by omega,?_⟩
  simp [tailRemaining]

#print axioms tail_remaining_step
#print axioms tail_body_progress
#print axioms tail_loop_spec
#print axioms tail_accumulation_spec
end UdonVerify.ProductBlock
