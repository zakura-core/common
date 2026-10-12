import CommonProductPairsBridges

open Aeneas Std Result
namespace UdonVerify.ProductPairs
open UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- An error-free finite observation of the actual iterator, ending at its first None. -/
inductive FiniteTrace {I Item : Type} (iterator : core.iter.traits.iterator.Iterator I Item) : I → List Item → Prop
  | done (iter after : I) (hnext : iterator.next iter = ok (none,after)) : FiniteTrace iterator iter []
  | more (iter after : I) (first : Item) (rest : List Item)
      (hnext : iterator.next iter = ok (some first,after)) (tail : FiniteTrace iterator after rest) :
      FiniteTrace iterator iter (first::rest)

theorem trace_nil {I Item : Type} (iterator : core.iter.traits.iterator.Iterator I Item) (iter : I)
    (trace : FiniteTrace iterator iter []) : ∃ after, iterator.next iter = ok (none,after) := by
  cases trace with
  | done _ after hnext => exact ⟨after,hnext⟩

theorem trace_cons {I Item : Type} (iterator : core.iter.traits.iterator.Iterator I Item) (iter : I)
    (first : Item) (rest : List Item) (trace : FiniteTrace iterator iter (first::rest)) :
    ∃ after, iterator.next iter = ok (some first,after) ∧ FiniteTrace iterator after rest := by
  cases trace with
  | more _ after _ _ hnext tail => exact ⟨after,hnext,tail⟩

def rawPairs {M S T : Type} (entries : List (Element M S × Element M T)) : Nat :=
  rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) (entries.map Prod.fst) (entries.map Prod.snd)

theorem raw_pairs_nil {M S T : Type} : rawPairs ([] : List (Element M S × Element M T)) = 0 := rfl

theorem raw_pairs_cons {M S T : Type} (a : Element M S) (b : Element M T)
    (rest : List (Element M S × Element M T)) :
    rawPairs ((a,b)::rest) = val4 a.limbs * val4 b.limbs + rawPairs rest := rfl

theorem pairs_loop_unfold {M S T I : Type} (inst : Modulus M)
    (iterator : core.iter.traits.iterator.Iterator I (Element M S × Element M T)) (iter : I) (sum : Sum M) :
    CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop inst iterator iter sum = (do
      let flow ← CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop.body inst iterator iter sum
      match flow with
      | .done out => ok out
      | .cont (next,updated) =>
        CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop inst iterator next updated) := by
  unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done out => rfl
  | cont state => rcases state with ⟨next,updated⟩; rfl

/-- No cardinality bound is needed: every overflow is folded by the public updater. -/
@[step]
theorem pair_loop_spec {M S T I : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (iterator : core.iter.traits.iterator.Iterator I (Element M S × Element M T)) (iter : I)
    (entries : List (Element M S × Element M T)) (trace : FiniteTrace iterator iter entries) (sum : Sum M) :
    CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop
      (portableDict inst) iterator iter sum ⦃ out =>
        Nat.ModEq (val4 params.modulus) (sumInteger out) (sumInteger sum + rawPairs entries) ⦄ := by
  induction trace generalizing sum with
  | done iter after hnext =>
    rw [pairs_loop_unfold]
    unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop.body
    rw [hnext]
    simp only [rawPairs,rawSum,WP.spec_ok,bind_ok,Std.uncurry,Std.uncurry_apply_pair,Nat.add_zero]
    exact Nat.ModEq.refl _
  | more iter after first rest hnext trace ih =>
    rcases first with ⟨lhs,rhs⟩
    rw [pairs_loop_unfold]
    unfold CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs_loop.body
    rw [hnext]
    simp only [bind_ok,Std.uncurry]
    step -grind with (pairs_add_spec inst params constants sum lhs rhs) as ⟨updated,hupdated⟩
    step -grind with (ih updated) as ⟨out,hout⟩
    simpa only [raw_pairs_cons,Nat.add_assoc] using hout.trans (hupdated.add_right (rawPairs rest))

#print axioms trace_nil
#print axioms trace_cons
#print axioms raw_pairs_nil
#print axioms raw_pairs_cons
#print axioms pairs_loop_unfold
#print axioms pair_loop_spec
end UdonVerify.ProductPairs
