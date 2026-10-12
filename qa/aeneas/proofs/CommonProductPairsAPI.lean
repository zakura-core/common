import CommonProductPairsShort

open Aeneas Std Result
namespace UdonVerify.ProductPairs
open UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- All short arms and an unrestricted finite tail of the production pair iterator. -/
@[step]
theorem pair_method_spec {M S T C I : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (into : core.iter.traits.collect.IntoIterator C (Element M S × Element M T) I)
    (source : C) (iter : I) (entries : List (Element M S × Element M T))
    (hinto : into.into_iter source = ok iter) (trace : FiniteTrace into.iteratorInst iter entries)
    (valid : ValidEntries (val4 params.modulus) s t entries) :
    sumOfPairs (portableDict inst) left right into source ⦃ out =>
      val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs) (rawPairs entries) ⦄ := by
  unfold sumOfPairs CommonProductPairs.field.pasta.products.PastaField.sum_of_product_pairs
  rw [hinto]
  simp only [bind_ok]
  cases entries with
  | nil =>
    obtain ⟨after,hnext⟩ := trace_nil into.iteratorInst iter trace
    rw [hnext]
    simp only [bind_ok,Std.uncurry,WP.spec_ok]
    constructor
    · have hp := params.positive
      simpa [CommonProductPairs.field.pasta.PastaField.ZERO,val4] using
        (show 0 < 2 * val4 params.modulus by omega)
    · simp [CommonProductPairs.field.pasta.PastaField.ZERO,val4,rawPairs,rawSum,Nat.ModEq]
  | cons first rest =>
    rcases first with ⟨a,b⟩
    obtain ⟨iter1,hnext,trace1⟩ := trace_cons into.iteratorInst iter (a,b) rest trace
    rw [hnext]
    simp only [bind_ok,Std.uncurry]
    cases rest with
    | nil =>
      obtain ⟨after,hnext1⟩ := trace_nil into.iteratorInst iter1 trace1
      rw [hnext1]
      simp only [bind_ok,Std.uncurry]
      rw [pairs_multiply_bridge]
      have ha := (valid (a,b) (by simp)).1
      have hb := (valid (a,b) (by simp)).2
      step -grind with (portable_multiply_spec (portableDict inst) params a b
        (entry_loose_bound _ s _ ha) (entry_loose_bound _ t _ hb)) as ⟨out,hout,hcert⟩
      exact ⟨hout,by simpa only [raw_pairs_cons,raw_pairs_nil,Nat.add_zero] using hcert⟩
    | cons second rest2 =>
      rcases second with ⟨c,d⟩
      obtain ⟨iter2,hnext2,trace2⟩ := trace_cons into.iteratorInst iter1 (c,d) rest2 trace1
      rw [hnext2]
      simp only [bind_ok,Std.uncurry]
      cases rest2 with
      | nil =>
        obtain ⟨after,hnext3⟩ := trace_nil into.iteratorInst iter2 trace2
        rw [hnext3]
        simp only [bind_ok,Std.uncurry,lift,Array.to_slice]
        exact short_pairs_spec inst params left right s t hs ht [(a,b),(c,d)] (by simp) valid
      | cons third rest3 =>
        rcases third with ⟨e,f⟩
        obtain ⟨iter3,hnext3,trace3⟩ := trace_cons into.iteratorInst iter2 (e,f) rest3 trace2
        rw [hnext3]
        simp only [bind_ok,Std.uncurry]
        cases rest3 with
        | nil =>
          obtain ⟨after,hnext4⟩ := trace_nil into.iteratorInst iter3 trace3
          rw [hnext4]
          simp only [bind_ok,Std.uncurry,lift,Array.to_slice]
          exact short_pairs_spec inst params left right s t hs ht [(a,b),(c,d),(e,f)] (by simp) valid
        | cons fourth tail =>
          rcases fourth with ⟨g,h⟩
          obtain ⟨iter4,hnext4,trace4⟩ := trace_cons into.iteratorInst iter3 (g,h) tail trace3
          rw [hnext4]
          simp only [bind_ok,Std.uncurry]
          have hfour := four_pairs_bound a c e g b d f h
          rw [pairs_new_bridge]
          step -grind with (portable_new_spec M) as ⟨sum,hzero⟩
          rw [pairs_bounded_bridge]
          step -grind with (portable_inner_bounded_spec inst params constants sum a b (by omega)) as ⟨sum1,hvalue1⟩
          rw [pairs_bounded_bridge]
          step -grind with (portable_inner_bounded_spec inst params constants sum1 c d (by omega)) as ⟨sum2,hvalue2⟩
          rw [pairs_bounded_bridge]
          step -grind with (portable_inner_bounded_spec inst params constants sum2 e f (by omega)) as ⟨sum3,hvalue3⟩
          rw [pairs_bounded_bridge]
          step -grind with (portable_inner_bounded_spec inst params constants sum3 g h (by omega)) as ⟨sum4,hvalue4⟩
          step -grind with (pair_loop_spec inst params constants into.iteratorInst iter4 tail trace4 sum4)
            as ⟨sum5,hmod⟩
          rw [pairs_finish_bridge]
          step -grind with (portable_finish_spec inst params constants sum5) as ⟨out,hout,hcert⟩
          refine ⟨hout,?_⟩
          have hexact : sumInteger sum4 + rawPairs tail = rawPairs ((a,b)::(c,d)::(e,f)::(g,h)::tail) := by
            simp only [raw_pairs_cons]
            omega
          simpa only [hexact] using hcert.trans hmod

def decodedPairs {M S T : Type} (p inverse : Nat) (entries : List (Element M S × Element M T)) : Nat :=
  rawSum (fun a => Native.decode p inverse a.limbs) (fun b => Native.decode p inverse b.limbs)
    (entries.map Prod.fst) (entries.map Prod.snd) % p

@[step]
theorem pair_method_value_spec {M S T C I : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (into : core.iter.traits.collect.IntoIterator C (Element M S × Element M T) I)
    (source : C) (iter : I) (entries : List (Element M S × Element M T))
    (hinto : into.into_iter source = ok iter) (trace : FiniteTrace into.iteratorInst iter entries)
    (valid : ValidEntries (val4 params.modulus) s t entries)
    (inverse : Nat) (hinverse : Nat.ModEq (val4 params.modulus) (R * inverse) 1) :
    sumOfPairs (portableDict inst) left right into source ⦃ out =>
      val4 out.limbs < 2 * val4 params.modulus ∧ Native.decode (val4 params.modulus) inverse out.limbs =
        decodedPairs (val4 params.modulus) inverse entries ⦄ := by
  apply WP.spec_mono (pair_method_spec inst params constants left right s t hs ht into source iter entries hinto trace valid)
  intro out hout
  refine ⟨hout.1,?_⟩
  have hscaled := Native.decoded_product_sum _ _ _ _ hinverse hout.2
  have hdecoded := raw_sum_decoded (fun a : Element M S => val4 a.limbs) (fun b : Element M T => val4 b.limbs)
    (val4 params.modulus) inverse (entries.map Prod.fst) (entries.map Prod.snd)
  exact hscaled.trans hdecoded.symm

#print axioms pair_method_spec
#print axioms pair_method_value_spec
end UdonVerify.ProductPairs
