import CommonProductPortableShortSteps

open Aeneas Std Result
namespace UdonVerify.ProductPortable
open UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def SerialLoopInvariant {M S T : Type} (total : Nat) (state : PairIter M S T × Sum M) : Prop :=
  state.1.fst.slice.length = state.1.snd.slice.length ∧
  state.1.fst.i = state.1.snd.i ∧
  state.1.fst.i ≤ state.1.fst.slice.length ∧
  sumInteger state.2 + remaining state.1 = total

def serialLoopMeasure {M S T : Type} (state : PairIter M S T × Sum M) : Nat :=
  state.1.fst.slice.length - state.1.fst.i

theorem portable_body_progress {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (total : Nat) (htotal : total < B ^ 9)
    (state : PairIter M S T × Sum M) (hinv : SerialLoopInvariant total state) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1.body
      (portableDict inst) state.1 state.2
      ⦃ flow => match flow with
        | .done out => sumInteger out = total
        | .cont next => SerialLoopInvariant total next ∧ serialLoopMeasure next < serialLoopMeasure state ⦄ := by
  rcases state with ⟨⟨⟨lhs,i⟩,⟨rhs,j⟩⟩,sum⟩
  rcases hinv with ⟨hlen,hij,hi,hvalue⟩
  dsimp only at hlen hij hi hvalue ⊢
  subst j
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1.body
  by_cases ha : i < lhs.length
  · have hb : i < rhs.length := by omega
    have hstep := remaining_step lhs rhs i ha hb
    rw [hstep] at hvalue
    have hbound : sumInteger sum + val4 (lhs[i]'ha).limbs * val4 (rhs[i]'hb).limbs < B ^ 9 := by omega
    rw [pair_next_some_eq lhs rhs i ha hb]
    simp only [bind_ok, Std.uncurry_apply_pair]
    step -grind with (portable_inner_bounded_spec inst params constants sum (lhs[i]'ha) (rhs[i]'hb) hbound)
      as ⟨out,hout⟩
    constructor
    · dsimp only [SerialLoopInvariant]
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
theorem portable_loop_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (total : Nat) (iter : PairIter M S T) (sum : Sum M)
    (htotal : total < B ^ 9) (hinv : SerialLoopInvariant total (iter,sum)) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1
      (portableDict inst) iter sum ⦃ out => sumInteger out = total ⦄ := by
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1
  apply loop.spec_decr_nat serialLoopMeasure (SerialLoopInvariant total) (fun out => sumInteger out = total)
  · intro state hstate
    have hprogress := portable_body_progress inst params constants total htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem portable_accumulation_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) (sum : Sum M)
    (hlen : lhs.length = rhs.length)
    (hbound : sumInteger sum + rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val < B ^ 9) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop1
      (portableDict inst) ⟨⟨lhs,0⟩,⟨rhs,0⟩⟩ sum
      ⦃ out => sumInteger out = sumInteger sum +
        rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val ⦄ := by
  apply portable_loop_spec inst params constants _ _ _ hbound
  dsimp only [SerialLoopInvariant]
  refine ⟨hlen,rfl,by omega,?_⟩
  simp [remaining]

#print axioms portable_body_progress
#print axioms portable_loop_spec
#print axioms portable_accumulation_spec
end UdonVerify.ProductPortable
