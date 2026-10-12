import CommonProductPortableLaneValues

open Aeneas Std Result
namespace UdonVerify.ProductPortable
open UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def ChunkLoopInvariant {M S T : Type} (total : Nat)
    (a : Aeneas.Std.Slice (Element M S)) (b : Aeneas.Std.Slice (Element M T))
    (state : ChunkIter M S T × Lanes M) : Prop :=
  state.1.fst.chunks.length = state.1.snd.chunks.length ∧
    (∀ c ∈ state.1.fst.chunks, c.length = 4) ∧
    (∀ c ∈ state.1.snd.chunks, c.length = 4) ∧
    state.1.fst.remainder = a ∧ state.1.snd.remainder = b ∧
    lanesInteger state.2 + chunkSum (fun x => val4 x.limbs) (fun y => val4 y.limbs)
      state.1.fst.chunks state.1.snd.chunks = total

def chunkLoopMeasure {M S T : Type} (state : ChunkIter M S T × Lanes M) : Nat :=
  state.1.fst.chunks.length

theorem chunk_body_progress {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (total : Nat) (a : Aeneas.Std.Slice (Element M S)) (b : Aeneas.Std.Slice (Element M T))
    (htotal : total < B ^ 9) (state : ChunkIter M S T × Lanes M)
    (hinv : ChunkLoopInvariant total a b state) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2.body
      (portableDict inst) state.1 state.2 ⦃ flow => match flow with
        | .done out => lanesInteger out = total
        | .cont next => ChunkLoopInvariant total a b next ∧ chunkLoopMeasure next < chunkLoopMeasure state ⦄ := by
  rcases state with ⟨⟨⟨lhs,ar⟩,⟨rhs,br⟩⟩,lanes⟩
  rcases hinv with ⟨hlen,ha,hb,har,hbr,hvalue⟩
  dsimp only at hlen ha hb har hbr hvalue ⊢
  cases lhs with
  | nil =>
    have hrhs : rhs = [] := by apply List.eq_nil_of_length_eq_zero; simpa using hlen.symm
    subst rhs
    unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2.body
    simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
      core.iter.traits.iterator.IteratorChunksExact, core.slice.iter.IteratorChunksExact.next, WP.spec_ok]
    simpa only [chunkSum, Nat.add_zero] using hvalue
  | cons x xs =>
    cases rhs with
    | nil => simp at hlen
    | cons y ys =>
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      have hbound : lanesInteger lanes + rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) x.val y.val < B ^ 9 := by
        simp only [chunkSum] at hvalue
        omega
      rw [lanes_body_cons_eq (portableDict inst) lanes x y xs ys ar br hx hy]
      step -grind with (add_four_spec inst params constants lanes x y hx hy hbound) as ⟨out,hout⟩
      constructor
      · dsimp only [ChunkLoopInvariant]
        refine ⟨by simpa using hlen, (fun c hc => ha c (by simp [hc])),
          (fun c hc => hb c (by simp [hc])), har, hbr, ?_⟩
        simp only [chunkSum] at hvalue
        omega
      · simp [chunkLoopMeasure]

@[step]
theorem chunk_loop_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (total : Nat) (a : Aeneas.Std.Slice (Element M S)) (b : Aeneas.Std.Slice (Element M T))
    (iter : ChunkIter M S T) (lanes : Lanes M) (htotal : total < B ^ 9)
    (hinv : ChunkLoopInvariant total a b (iter,lanes)) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2
      (portableDict inst) iter lanes ⦃ out => lanesInteger out = total ⦄ := by
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2
  apply loop.spec_decr_nat chunkLoopMeasure (ChunkLoopInvariant total a b) (fun out => lanesInteger out = total)
  · intro state hstate
    have hprogress := chunk_body_progress inst params constants total a b htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem chunk_accumulation_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (iter : ChunkIter M S T) (lanes : Lanes M)
    (hlen : iter.fst.chunks.length = iter.snd.chunks.length)
    (ha : ∀ c ∈ iter.fst.chunks, c.length = 4) (hb : ∀ c ∈ iter.snd.chunks, c.length = 4)
    (hbound : lanesInteger lanes + chunkSum (fun x => val4 x.limbs) (fun y => val4 y.limbs)
      iter.fst.chunks iter.snd.chunks < B ^ 9) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice_loop2
      (portableDict inst) iter lanes ⦃ out => lanesInteger out = lanesInteger lanes +
        chunkSum (fun x => val4 x.limbs) (fun y => val4 y.limbs) iter.fst.chunks iter.snd.chunks ⦄ := by
  apply chunk_loop_spec inst params constants _ iter.fst.remainder iter.snd.remainder _ _ hbound
  exact ⟨hlen,ha,hb,rfl,rfl,rfl⟩

#print axioms chunk_body_progress
#print axioms chunk_loop_spec
#print axioms chunk_accumulation_spec
end UdonVerify.ProductPortable
