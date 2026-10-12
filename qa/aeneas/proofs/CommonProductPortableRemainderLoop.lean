import CommonProductPortableRemainderBody

open Aeneas Std Result
namespace UdonVerify.ProductPortable
open UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def RemainderLoopInvariant {M S T : Type} (total : Nat) (state : PairIter M S T × Lanes M) : Prop :=
  state.1.fst.slice.length = state.1.snd.slice.length ∧
  state.1.fst.i = state.1.snd.i ∧
  state.1.fst.i ≤ state.1.fst.slice.length ∧
  lanesInteger state.2 + remaining state.1 = total

def remainderLoopMeasure {M S T : Type} (state : PairIter M S T × Lanes M) : Nat :=
  state.1.fst.slice.length - state.1.fst.i

theorem remainder_body_progress {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (total : Nat) (htotal : total < B ^ 9)
    (state : PairIter M S T × Lanes M) (hinv : RemainderLoopInvariant total state) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3.body
      (portableDict inst) state.1 state.2
      ⦃ flow => match flow with
        | .done out => lanesInteger out = total
        | .cont next => RemainderLoopInvariant total next ∧ remainderLoopMeasure next < remainderLoopMeasure state ⦄ := by
  rcases state with ⟨⟨⟨lhs,i⟩,⟨rhs,j⟩⟩,sum⟩
  rcases hinv with ⟨hlen,hij,hi,hvalue⟩
  dsimp only at hlen hij hi hvalue ⊢
  subst j
  rw [remainder_body_eq]
  unfold remainderBody
  by_cases ha : i < lhs.length
  · have hb : i < rhs.length := by omega
    have hstep := remaining_step lhs rhs i ha hb
    rw [hstep] at hvalue
    have hbound : lanesInteger sum + val4 (lhs[i]'ha).limbs * val4 (rhs[i]'hb).limbs < B ^ 9 := by omega
    rw [pair_next_some_eq lhs rhs i ha hb]
    simp only [bind_ok, Std.uncurry_apply_pair]
    have hbound0 : sumInteger sum[0]! + val4 (lhs[i]'ha).limbs * val4 (rhs[i]'hb).limbs < B ^ 9 := by
      unfold lanesInteger at hbound
      omega
    step -grind with (portable_inner_bounded_spec inst params constants sum[0]! (lhs[i]'ha) (rhs[i]'hb) hbound0)
      as ⟨out,hout⟩
    have hupdate := lanes_set_zero_value sum out
    have hvalueOut : lanesInteger (sum.set 0#usize out) = lanesInteger sum +
        val4 (lhs[i]'ha).limbs * val4 (rhs[i]'hb).limbs := by omega
    constructor
    · dsimp only [RemainderLoopInvariant]
      refine ⟨hlen,rfl,by omega,?_⟩
      omega
    · change lhs.length - (i+1) < lhs.length - i
      omega
  · have hindex : i = lhs.length := by omega
    have hremaining : remaining (⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ : PairIter M S T) = 0 := by
      simp [remaining, hindex, rawSum]
    rw [pair_next_none_eq lhs rhs i (by omega)]
    simp only [bind_ok, Std.uncurry_apply_pair, WP.spec_ok]
    simpa only [hremaining, Nat.add_zero] using hvalue

@[step]
theorem remainder_loop_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (total : Nat) (iter : PairIter M S T) (sum : Lanes M)
    (htotal : total < B ^ 9) (hinv : RemainderLoopInvariant total (iter,sum)) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3
      (portableDict inst) iter sum ⦃ out => lanesInteger out = total ⦄ := by
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3
  apply loop.spec_decr_nat remainderLoopMeasure (RemainderLoopInvariant total) (fun out => lanesInteger out = total)
  · intro state hstate
    have hprogress := remainder_body_progress inst params constants total htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem remainder_accumulation_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) (sum : Lanes M)
    (hlen : lhs.length = rhs.length)
    (hbound : lanesInteger sum + rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val < B ^ 9) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop3
      (portableDict inst) ⟨⟨lhs,0⟩,⟨rhs,0⟩⟩ sum
      ⦃ out => lanesInteger out = lanesInteger sum +
        rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val ⦄ := by
  apply remainder_loop_spec inst params constants _ _ _ hbound
  dsimp only [RemainderLoopInvariant]
  refine ⟨hlen,rfl,by omega,?_⟩
  simp [remaining]

#print axioms remainder_body_progress
#print axioms remainder_loop_spec
#print axioms remainder_accumulation_spec
end UdonVerify.ProductPortable
