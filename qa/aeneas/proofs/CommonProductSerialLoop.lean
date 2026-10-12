import CommonProductSerialPrimitives
import CommonProductSliceMath

open Aeneas Std Result
namespace UdonVerify.ProductSerial
open UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev PairIter (M S T : Type) := core.iter.adapters.zip.Zip
  (core.slice.iter.Iter (Element M S)) (core.slice.iter.Iter (Element M T))

def remaining {M S T : Type} (iter : PairIter M S T) : Nat :=
  rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs)
    (iter.fst.slice.val.drop iter.fst.i) (iter.snd.slice.val.drop iter.snd.i)

theorem pair_next_some_eq {M S T : Type} (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (i : Nat) (ha : i < lhs.length) (hb : i < rhs.length) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (Element M S))
      (core.iter.traits.iterator.IteratorSliceIter (Element M T))
      ⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ =
      ok (some (lhs[i]'ha,rhs[i]'hb),⟨⟨lhs,i+1⟩,⟨rhs,i+1⟩⟩) := by
  simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next, ha, hb]
  constructor <;> rfl

theorem pair_next_none_eq {M S T : Type} (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (i : Nat) (ha : lhs.length ≤ i) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter (Element M S))
      (core.iter.traits.iterator.IteratorSliceIter (Element M T))
      ⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ = ok (none,⟨⟨lhs,i⟩,⟨rhs,i⟩⟩) := by
  simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.iter.traits.iterator.IteratorSliceIter, core.slice.iter.IteratorSliceIter.next,
    show ¬ i < lhs.length by omega]

theorem remaining_step {M S T : Type} (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (i : Nat) (ha : i < lhs.length) (hb : i < rhs.length) :
    remaining (⟨⟨lhs,i⟩,⟨rhs,i⟩⟩ : PairIter M S T) =
      val4 (lhs[i]'ha).limbs * val4 (rhs[i]'hb).limbs +
        remaining (⟨⟨lhs,i+1⟩,⟨rhs,i+1⟩⟩ : PairIter M S T) := by
  unfold remaining
  dsimp only
  rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb]
  rfl

def SliceLoopInvariant {M S T : Type} (total : Nat) (state : PairIter M S T × Sum M) : Prop :=
  state.1.fst.slice.length = state.1.snd.slice.length ∧
  state.1.fst.i = state.1.snd.i ∧
  state.1.fst.i ≤ state.1.fst.slice.length ∧
  sumInteger state.2 + remaining state.1 = total

def sliceLoopMeasure {M S T : Type} (state : PairIter M S T × Sum M) : Nat :=
  state.1.fst.slice.length - state.1.fst.i

theorem serial_body_progress {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (total : Nat) (htotal : total < B ^ 9)
    (state : PairIter M S T × Sum M) (hinv : SliceLoopInvariant total state) :
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice_loop.body
      (serialDict inst) state.1 state.2
      ⦃ flow => match flow with
        | .done out => sumInteger out = total
        | .cont next => SliceLoopInvariant total next ∧ sliceLoopMeasure next < sliceLoopMeasure state ⦄ := by
  rcases state with ⟨⟨⟨lhs,i⟩,⟨rhs,j⟩⟩,sum⟩
  rcases hinv with ⟨hlen,hij,hi,hvalue⟩
  dsimp only at hlen hij hi hvalue ⊢
  subst j
  unfold CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice_loop.body
  by_cases ha : i < lhs.length
  · have hb : i < rhs.length := by omega
    have hstep := remaining_step lhs rhs i ha hb
    rw [hstep] at hvalue
    have hbound : sumInteger sum + val4 (lhs[i]'ha).limbs * val4 (rhs[i]'hb).limbs < B ^ 9 := by omega
    rw [pair_next_some_eq lhs rhs i ha hb]
    simp only [bind_ok, Std.uncurry_apply_pair]
    step -grind with (serial_inner_bounded_spec inst params constants sum (lhs[i]'ha) (rhs[i]'hb) hbound)
      as ⟨out,hout⟩
    constructor
    · dsimp only [SliceLoopInvariant]
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
theorem serial_loop_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (total : Nat) (iter : PairIter M S T) (sum : Sum M)
    (htotal : total < B ^ 9) (hinv : SliceLoopInvariant total (iter,sum)) :
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice_loop
      (serialDict inst) iter sum ⦃ out => sumInteger out = total ⦄ := by
  unfold CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice_loop
  apply loop.spec_decr_nat sliceLoopMeasure (SliceLoopInvariant total) (fun out => sumInteger out = total)
  · intro state hstate
    have hprogress := serial_body_progress inst params constants total htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem serial_accumulation_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T)) (sum : Sum M)
    (hlen : lhs.length = rhs.length)
    (hbound : sumInteger sum + rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val < B ^ 9) :
    CommonProductSerial.field.pasta.products.PastaField.sum_of_products_slice_loop
      (serialDict inst) ⟨⟨lhs,0⟩,⟨rhs,0⟩⟩ sum
      ⦃ out => sumInteger out = sumInteger sum +
        rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val ⦄ := by
  apply serial_loop_spec inst params constants _ _ _ hbound
  dsimp only [SliceLoopInvariant]
  refine ⟨hlen,rfl,by omega,?_⟩
  simp [remaining]

#print axioms pair_next_some_eq
#print axioms pair_next_none_eq
#print axioms remaining_step
#print axioms serial_body_progress
#print axioms serial_loop_spec
#print axioms serial_accumulation_spec
end UdonVerify.ProductSerial
