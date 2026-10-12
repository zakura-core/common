import CommonProductPairsAPI

open Aeneas Std Result
namespace UdonVerify.ProductWrappers
open UdonVerify.ProductPairs UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- The same transparent standard Zip dictionary selected by the extracted call. -/
def zipIterator {I J A B : Type} (left : core.iter.traits.iterator.Iterator I A)
    (right : core.iter.traits.iterator.Iterator J B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.zip.Zip I J) (A × B) :=
  CommonProductPairs.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair left right

theorem zip_finite_trace {I J A B : Type} (left : core.iter.traits.iterator.Iterator I A)
    (right : core.iter.traits.iterator.Iterator J B) (il : I) (ir : J)
    (xs : List A) (ys : List B) (tl : FiniteTrace left il xs) (tr : FiniteTrace right ir ys)
    (hlen : xs.length = ys.length) :
    FiniteTrace (zipIterator left right) (⟨il,ir⟩ : core.iter.adapters.zip.Zip I J) (xs.zip ys) := by
  induction tl generalizing ir ys with
  | done il after hnext =>
    simp only [List.zip_nil_left]
    apply FiniteTrace.done _ ⟨after,ir⟩
    simp [zipIterator,CommonProductPairs.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair,
      core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,hnext]
  | more il after first rest hnext tail ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      obtain ⟨afterR,hright,tright⟩ := trace_cons right ir y ys tr
      apply FiniteTrace.more _ ⟨after,afterR⟩ (first,y) (rest.zip ys)
      · simp [zipIterator,CommonProductPairs.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair,
          core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,hnext,hright]
      · apply ih afterR ys tright
        simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen

theorem raw_sum_zip_components {A B : Type} (a : A → Nat) (b : B → Nat)
    (xs : List A) (ys : List B) :
    rawSum a b ((xs.zip ys).map Prod.fst) ((xs.zip ys).map Prod.snd) = rawSum a b xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.zip_cons_cons,List.map_cons,rawSum]
      rw [ih]

theorem decoded_pairs_zip {M S T : Type} (p inverse : Nat)
    (xs : List (Element M S)) (ys : List (Element M T)) :
    decodedPairs p inverse (xs.zip ys) =
      rawSum (fun a => Native.decode p inverse a.limbs)
        (fun b => Native.decode p inverse b.limbs) xs ys % p := by
  unfold decodedPairs
  rw [raw_sum_zip_components]

theorem valid_entries_zip {M S T : Type} (p : Nat) (s t : Bool)
    (xs : List (Element M S)) (ys : List (Element M T))
    (ha : ∀ a ∈ xs, val4 a.limbs < stateWeight s * p)
    (hb : ∀ b ∈ ys, val4 b.limbs < stateWeight t * p) :
    ValidEntries p s t (xs.zip ys) := by
  intro pair hm
  rcases pair with ⟨a,b⟩
  obtain ⟨hl,hr⟩ := List.of_mem_zip hm
  exact ⟨ha a hl,hb b hr⟩

#print axioms zip_finite_trace
#print axioms raw_sum_zip_components
#print axioms decoded_pairs_zip
#print axioms valid_entries_zip
end UdonVerify.ProductWrappers
