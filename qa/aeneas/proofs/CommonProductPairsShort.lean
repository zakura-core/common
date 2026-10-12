import CommonProductPairTrace

open Aeneas Std Result
namespace UdonVerify.ProductPairs
open UdonVerify.ProductPortable UdonVerify.Products
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev pairLeftSlice {M S T : Type} (entries : List (Element M S × Element M T))
    (hsize : entries.length ≤ 3) : Aeneas.Std.Slice (Element M S) :=
  Aeneas.Std.Slice.from (entries.map Prod.fst) (by simp only [List.length_map]; scalar_tac)

abbrev pairRightSlice {M S T : Type} (entries : List (Element M S × Element M T))
    (hsize : entries.length ≤ 3) : Aeneas.Std.Slice (Element M T) :=
  Aeneas.Std.Slice.from (entries.map Prod.snd) (by simp only [List.length_map]; scalar_tac)

def ValidEntries {M S T : Type} (p : Nat) (s t : Bool)
    (entries : List (Element M S × Element M T)) : Prop :=
  ∀ pair ∈ entries, val4 pair.1.limbs < stateWeight s * p ∧ val4 pair.2.limbs < stateWeight t * p

theorem entry_loose_bound (p : Nat) (state : Bool) (value : Nat)
    (hbound : value < stateWeight state * p) : value < 2 * p := by
  cases state <;> simp only [stateWeight,Bool.false_eq_true,↓reduceIte,one_mul] at hbound <;> omega

@[step]
theorem short_pairs_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (left : State S) (right : State T) (s t : Bool)
    (hs : left.sealedSealedInst.REDUCED = ok s) (ht : right.sealedSealedInst.REDUCED = ok t)
    (entries : List (Element M S × Element M T)) (hsize : entries.length ≤ 3)
    (valid : ValidEntries (val4 params.modulus) s t entries) :
    CommonProductPairs.field.pasta.products.PastaField.sum_of_products_slice
      (portableDict inst) left right (pairLeftSlice entries hsize) (pairRightSlice entries hsize)
      ⦃ out => val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs) (rawPairs entries) ⦄ := by
  rw [pairs_slice_bridge]
  have ha : ∀ a ∈ (pairLeftSlice entries hsize).val, val4 a.limbs < stateWeight s * val4 params.modulus := by
    intro a ha
    simp only [pairLeftSlice,Aeneas.Std.Slice.from_val] at ha
    rcases List.mem_map.mp ha with ⟨pair,hpair,rfl⟩
    exact (valid pair hpair).1
  have hb : ∀ b ∈ (pairRightSlice entries hsize).val, val4 b.limbs < stateWeight t * val4 params.modulus := by
    intro b hb
    simp only [pairRightSlice,Aeneas.Std.Slice.from_val] at hb
    rcases List.mem_map.mp hb with ⟨pair,hpair,rfl⟩
    exact (valid pair hpair).2
  have hspec := slice_short_spec inst params left right s t hs ht
    (pairLeftSlice entries hsize) (pairRightSlice entries hsize)
    (by simp [pairLeftSlice,pairRightSlice,Aeneas.Std.Slice.length])
    (by simpa [pairLeftSlice,Aeneas.Std.Slice.length] using hsize) ha hb
  simpa only [rawPairs,pairLeftSlice,pairRightSlice,Aeneas.Std.Slice.from_val] using hspec

theorem four_pairs_bound {M S T : Type} (a c e g : Element M S) (b d f h : Element M T) :
    val4 a.limbs * val4 b.limbs + val4 c.limbs * val4 d.limbs +
      val4 e.limbs * val4 f.limbs + val4 g.limbs * val4 h.limbs < B ^ 9 := by
  have hsum := bounded_sum_fits_accumulator (fun a : Element M S => val4 a.limbs)
    (fun b : Element M T => val4 b.limbs) [a,c,e,g] [b,d,f,h] (by rfl) (by norm_num [B])
    (fun x _ => val4_lt x.limbs) (fun y _ => val4_lt y.limbs)
  simpa only [rawSum,Nat.add_zero,Nat.add_assoc] using hsum

#print axioms entry_loose_bound
#print axioms short_pairs_spec
#print axioms four_pairs_bound
end UdonVerify.ProductPairs
