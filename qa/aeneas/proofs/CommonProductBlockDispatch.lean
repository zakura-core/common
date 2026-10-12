import CommonProductBlockKernel
import CommonProductBlockChunks

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Matching chunk lengths preserve the ungrouped integer sum. -/
theorem block_chunk_sum_flatten {α β : Type} (left : α → Nat) (right : β → Nat)
    (lhs : List (Aeneas.Std.Slice α)) (rhs : List (Aeneas.Std.Slice β))
    (hshape : lhs.map (fun a => a.length) = rhs.map (fun b => b.length)) :
    chunkSum left right lhs rhs = rawSum left right
      ((lhs.map (fun a => a.val)).flatten) ((rhs.map (fun b => b.val)).flatten) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> simp_all [chunkSum,rawSum]
  | cons x xs ih =>
    cases rhs with
    | nil => simp at hshape
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at hshape
      have htail := ih ys hshape.2
      simp only [chunkSum,List.map_cons,List.flatten_cons]
      rw [raw_sum_append left right x.val _ y.val _ hshape.1,← htail]

abbrev BlockIter (M S T : Type) := core.iter.adapters.zip.Zip
  (BlockChunks (Element M S)) (BlockChunks (Element M T))

def BlockInvariant {M S T : Type} (total : Nat) (state : BlockIter M S T × Sum M) : Prop :=
  state.1.fst.chunks.map (fun a => a.length) = state.1.snd.chunks.map (fun a => a.length) ∧
    (∀ a ∈ state.1.fst.chunks, a.length ≤ 32) ∧
    sumInteger state.2 + chunkSum (fun a => val4 a.limbs) (fun b => val4 b.limbs)
      state.1.fst.chunks state.1.snd.chunks = total

def blockMeasure {M S T : Type} (state : BlockIter M S T × Sum M) : Nat :=
  state.1.fst.chunks.length

theorem block_next_some {M S T : Type}
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (xs : List (Aeneas.Std.Slice (Element M S))) (ys : List (Aeneas.Std.Slice (Element M T))) :
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (CommonProductsAarch64.core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice (Element M S))
      (CommonProductsAarch64.core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice (Element M T))
      (⟨⟨lhs::xs⟩,⟨rhs::ys⟩⟩ : BlockIter M S T) =
      ok (some (lhs,rhs),⟨⟨xs⟩,⟨ys⟩⟩) := by
  simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    CommonProductsAarch64.core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice,
    CommonProductsAarch64.core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next]

theorem block_body_progress {M S T : Type} (total : Nat) (htotal : total < B ^ 9)
    (state : BlockIter M S T × Sum M) (hinv : BlockInvariant total state) :
    CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice_loop1.body
      state.1 state.2 ⦃ flow => match flow with
        | .done out => sumInteger out = total
        | .cont next => BlockInvariant total next ∧ blockMeasure next < blockMeasure state ⦄ := by
  rcases state with ⟨⟨⟨lhs⟩,⟨rhs⟩⟩,sum⟩
  rcases hinv with ⟨hshape,hbound,hvalue⟩
  dsimp only at hshape hbound hvalue ⊢
  cases lhs with
  | nil =>
    have hrhs : rhs = [] := by
      cases rhs with
      | nil => rfl
      | cons y ys => simp at hshape
    subst rhs
    unfold CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice_loop1.body
    simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
      CommonProductsAarch64.core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice,
      CommonProductsAarch64.core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,
      WP.spec_ok]
    simpa only [chunkSum,Nat.add_zero] using hvalue
  | cons x xs =>
    cases rhs with
    | nil => simp at hshape
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at hshape
      have hx := hbound x (by simp)
      have hfirst : sumInteger sum + rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) x.val y.val < B ^ 9 := by
        simp only [chunkSum] at hvalue
        omega
      unfold CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice_loop1.body
      rw [block_next_some]
      simp only [bind_ok,Std.uncurry_apply_pair]
      step -grind with (block_kernel_spec sum x y hshape.1 hx hfirst) as ⟨out,hout⟩
      constructor
      · dsimp only [BlockInvariant]
        refine ⟨hshape.2,(fun c hc => hbound c (by simp [hc])),?_⟩
        simp only [chunkSum] at hvalue
        omega
      · simp [blockMeasure]

@[step]
theorem block_loop_spec {M S T : Type} (total : Nat) (iter : BlockIter M S T) (sum : Sum M)
    (htotal : total < B ^ 9) (hinv : BlockInvariant total (iter,sum)) :
    CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice_loop1 iter sum
      ⦃ out => sumInteger out = total ⦄ := by
  unfold CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice_loop1
  apply loop.spec_decr_nat blockMeasure (BlockInvariant total) (fun out => sumInteger out = total)
  · intro state hstate
    have hprogress := block_body_progress total htotal state hstate
    simp only [Std.uncurry] at hprogress ⊢
    apply WP.spec_mono hprogress
    intro flow hflow
    cases flow <;> exact hflow
  · exact hinv

@[step]
theorem block_accumulation_spec {M S T : Type} (iter : BlockIter M S T) (sum : Sum M)
    (hshape : iter.fst.chunks.map (fun a => a.length) = iter.snd.chunks.map (fun b => b.length))
    (hsize : ∀ a ∈ iter.fst.chunks, a.length ≤ 32)
    (hbound : sumInteger sum + chunkSum (fun a => val4 a.limbs) (fun b => val4 b.limbs)
      iter.fst.chunks iter.snd.chunks < B ^ 9) :
    CommonProductsAarch64.field.pasta.products.PastaField.sum_of_products_slice_loop1 iter sum
      ⦃ out => sumInteger out = sumInteger sum + chunkSum (fun a => val4 a.limbs) (fun b => val4 b.limbs)
        iter.fst.chunks iter.snd.chunks ⦄ := by
  apply block_loop_spec _ iter sum hbound
  exact ⟨hshape,hsize,rfl⟩

#print axioms block_chunk_sum_flatten
#print axioms block_next_some
#print axioms block_body_progress
#print axioms block_loop_spec
#print axioms block_accumulation_spec
end UdonVerify.ProductBlock
