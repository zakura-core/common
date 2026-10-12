import CommonProductBlockIteration

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def quadValue {M S T : Type} (li ri : Usize) (lhs : Quad M S) (rhs : Quad M T) : Nat :=
  wordDot (fun a => a.limbs) (fun b => b.limbs) li.val ri.val lhs.val rhs.val

theorem quad_value_four {M S T : Type} (li ri : Usize) (lhs : Quad M S) (rhs : Quad M T) :
    quadValue li ri lhs rhs =
      lhs[0]!.limbs[li.val]!.val * rhs[0]!.limbs[ri.val]!.val +
      lhs[1]!.limbs[li.val]!.val * rhs[1]!.limbs[ri.val]!.val +
      lhs[2]!.limbs[li.val]!.val * rhs[2]!.limbs[ri.val]!.val +
      lhs[3]!.limbs[li.val]!.val * rhs[3]!.limbs[ri.val]!.val := by
  rw [UdonVerify.ProductPortable.array_four_eta_generic lhs,
    UdonVerify.ProductPortable.array_four_eta_generic rhs]
  simp only [quadValue,wordDot,Array.make_val,rawSum,Array.getElem!_Nat_eq,
    List.getElem!_cons_zero,List.getElem!_cons_succ]
  omega

@[step]
theorem add_quad_spec {M S T : Type} (li ri : Usize) (columns : BatchColumns)
    (lhs : Quad M S) (rhs : Quad M T) (hi : li.val < 4) (hj : ri.val < 4)
    (hbound : batchColumnsInteger columns + quadValue li ri lhs rhs < B ^ 3) :
    addQuad li ri columns lhs rhs ⦃ out =>
      batchColumnsInteger out = batchColumnsInteger columns + quadValue li ri lhs rhs ⦄ := by
  have hraw := quad_value_four li ri lhs rhs
  rw [hraw] at hbound ⊢
  unfold addQuad
  step -grind with (add_at_spec 0#usize li ri columns lhs[0]! rhs[0]! (by decide) hi hj (by omega))
    as ⟨a,ha⟩
  step -grind with (add_at_spec 1#usize li ri a lhs[1]! rhs[1]! (by decide) hi hj (by omega))
    as ⟨b,hb⟩
  step -grind with (add_at_spec 2#usize li ri b lhs[2]! rhs[2]! (by decide) hi hj (by omega))
    as ⟨c,hc⟩
  step -grind with (add_at_spec 3#usize li ri c lhs[3]! rhs[3]! (by decide) hi hj (by omega))
    as ⟨out,hout⟩
  omega

/-- Unprocessed pairs of complete four-element arrays. -/
def quadSum {M S T : Type} (li ri : Usize) : List (Quad M S) → List (Quad M T) → Nat
  | a::xs,b::ys => quadValue li ri a b + quadSum li ri xs ys
  | _,_ => 0

def quadRemaining {M S T : Type} (li ri : Usize) (it : QuadIter M S T) : Nat :=
  quadSum li ri (it.fst.slice.val.drop it.fst.i) (it.snd.slice.val.drop it.snd.i)

def QuadInvariant {M S T : Type} (li ri : Usize) (total : Nat)
    (state : QuadIter M S T × BatchColumns) : Prop :=
  state.1.fst.slice.length = state.1.snd.slice.length ∧
    state.1.fst.i = state.1.snd.i ∧ state.1.fst.i ≤ state.1.fst.slice.length ∧
    batchColumnsInteger state.2 + quadRemaining li ri state.1 = total

def quadMeasure {M S T : Type} (state : QuadIter M S T × BatchColumns) : Nat :=
  state.1.fst.slice.length - state.1.fst.i

theorem quad_remaining_step {M S T : Type} (li ri : Usize)
    (lhs : Aeneas.Std.Slice (Quad M S)) (rhs : Aeneas.Std.Slice (Quad M T))
    (i : Nat) (ha : i < lhs.length) (hb : i < rhs.length) :
    quadRemaining li ri (⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ : QuadIter M S T) =
      quadValue li ri (lhs[i]'ha) (rhs[i]'hb) +
        quadRemaining li ri (⟨⟨lhs,i+1⟩,⟨rhs,i+1⟩⟩ : QuadIter M S T) := by
  unfold quadRemaining
  dsimp only
  rw [List.drop_eq_getElem_cons ha,List.drop_eq_getElem_cons hb]
  rfl

theorem quad_body_progress {M S T : Type} (li ri : Usize) (hi : li.val < 4) (hj : ri.val < 4)
    (total : Nat) (htotal : total < B ^ 3) (state : QuadIter M S T × BatchColumns)
    (hinv : QuadInvariant li ri total state) :
    quadBody li ri state.1 state.2 ⦃ flow => match flow with
      | .done out => batchColumnsInteger out = total
      | .cont next => QuadInvariant li ri total next ∧ quadMeasure next < quadMeasure state ⦄ := by
  rcases state with ⟨⟨⟨lhs,i⟩,⟨rhs,j⟩⟩,columns⟩
  rcases hinv with ⟨hlen,hij,hidx,hvalue⟩
  dsimp only at hlen hij hidx hvalue ⊢
  subst j
  by_cases ha : i < lhs.length
  · have hb : i < rhs.length := by omega
    have hstep := quad_remaining_step li ri lhs rhs i ha hb
    rw [hstep] at hvalue
    rw [quad_body_some_eq li ri _ _ columns _ _ (slice_pair_next_some lhs rhs i ha hb)]
    step -grind with (add_quad_spec li ri columns (lhs[i]'ha) (rhs[i]'hb) hi hj (by omega))
      as ⟨out,hout⟩
    constructor
    · dsimp only [QuadInvariant]
      exact ⟨hlen,rfl,by omega,by omega⟩
    · change lhs.length - (i+1) < lhs.length - i
      omega
  · unfold quadBody
    rw [slice_pair_next_none lhs rhs i (by omega)]
    simp only [bind_ok,Std.uncurry_apply_pair,WP.spec_ok]
    have hrem : quadRemaining li ri (⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ : QuadIter M S T) = 0 := by
      simp [quadRemaining, show i = lhs.length from by omega, quadSum]
    omega

@[step]
theorem quad_loop_spec {M S T : Type} (li ri : Usize) (hi : li.val < 4) (hj : ri.val < 4)
    (total : Nat) (iter : QuadIter M S T) (columns : BatchColumns) (htotal : total < B ^ 3)
    (hinv : QuadInvariant li ri total (iter,columns)) :
    quadLoop li ri iter columns ⦃ out => batchColumnsInteger out = total ⦄ := by
  unfold quadLoop
  apply loop.spec_decr_nat quadMeasure (QuadInvariant li ri total) (fun out => batchColumnsInteger out = total)
  · intro state hstate
    have hprogress := quad_body_progress li ri hi hj total htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem quad_accumulation_spec {M S T : Type} (li ri : Usize) (hi : li.val < 4) (hj : ri.val < 4)
    (lhs : Aeneas.Std.Slice (Quad M S)) (rhs : Aeneas.Std.Slice (Quad M T)) (columns : BatchColumns)
    (hlen : lhs.length = rhs.length)
    (hbound : batchColumnsInteger columns + quadSum li ri lhs.val rhs.val < B ^ 3) :
    quadLoop li ri ⟨⟨lhs,0⟩,⟨rhs,0⟩⟩ columns ⦃ out =>
      batchColumnsInteger out = batchColumnsInteger columns + quadSum li ri lhs.val rhs.val ⦄ := by
  apply quad_loop_spec li ri hi hj _ _ _ hbound
  dsimp only [QuadInvariant]
  refine ⟨hlen,rfl,by omega,?_⟩
  simp [quadRemaining]

#print axioms quad_value_four
#print axioms add_quad_spec
#print axioms quad_remaining_step
#print axioms quad_body_progress
#print axioms quad_loop_spec
#print axioms quad_accumulation_spec
end UdonVerify.ProductBlock
