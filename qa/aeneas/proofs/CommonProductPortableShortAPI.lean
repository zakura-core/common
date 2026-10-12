import CommonProductPortableShortLoop
import CommonProductPortableShortFinalization

open Aeneas Std Result
namespace UdonVerify.ProductPortable
open UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev State := CommonProductsPortable.field.pasta.representation.ReductionState

theorem state_weight_le_two (state : Bool) : stateWeight state ≤ 2 := by cases state <;> decide

@[step]
theorem slice_short_spec {M S T : Type} (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (left : State S) (right : State T)
    (s t : Bool) (hs : left.sealedSealedInst.REDUCED = ok s)
    (ht : right.sealedSealedInst.REDUCED = ok t)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length) (hshort : lhs.length ≤ 3)
    (ha : ∀ a ∈ lhs.val, val4 a.limbs < stateWeight s * val4 params.modulus)
    (hb : ∀ b ∈ rhs.val, val4 b.limbs < stateWeight t * val4 params.modulus) :
    CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice
      (portableDict inst) left right lhs rhs ⦃ out =>
        val4 out.limbs < 2 * val4 params.modulus ∧
        Nat.ModEq (val4 params.modulus) (R * val4 out.limbs)
          (rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val) ⦄ := by
  have hlenU : Aeneas.Std.Slice.len lhs = Aeneas.Std.Slice.len rhs :=
    UScalar.eq_of_val_eq (by simpa only [Aeneas.Std.Slice.len_val] using hlen)
  have hsmallU : Aeneas.Std.Slice.len lhs ≤ 3#usize := by scalar_tac
  have hbits : core.num.Usize.BITS ≤ 64#u32 := by
    change (core.num.Usize.BITS).val ≤ 64
    simpa [core.num.Usize.BITS] using System.Platform.numBits_le
  have haLoose : ∀ a ∈ lhs.val, val4 a.limbs < 2 * val4 params.modulus := fun a hm =>
    _root_.lt_of_lt_of_le (ha a hm) (Nat.mul_le_mul_right _ (state_weight_le_two s))
  have hbLoose : ∀ b ∈ rhs.val, val4 b.limbs < 2 * val4 params.modulus := fun b hm =>
    _root_.lt_of_lt_of_le (hb b hm) (Nat.mul_le_mul_right _ (state_weight_le_two t))
  have hwideBound := short_sum_wide_bound inst params (fun a => val4 a.limbs) (fun b => val4 b.limbs)
    lhs.val rhs.val hlen hshort haLoose hbLoose
  unfold CommonProductsPortable.field.pasta.products.PastaField.sum_of_products_slice
  simp only [← hlenU]
  simp [hbits, hsmallU, core.slice.Slice.is_empty, massert]
  by_cases hempty : lhs.val = []
  · rw [if_pos hempty]
    simp only [WP.spec_ok]
    have hp := params.positive
    constructor
    · simpa [CommonProductsPortable.field.pasta.PastaField.ZERO, val4] using
        (show 0 < 2 * val4 params.modulus by omega)
    · simp [CommonProductsPortable.field.pasta.PastaField.ZERO, val4, Nat.ModEq, hempty, rawSum]
  · rw [if_neg hempty]
    by_cases hone : Aeneas.Std.Slice.len lhs = 1#usize
    · rw [if_pos hone]
      have hleftLength : lhs.val.length = 1 := by
        simpa using congrArg UScalar.val hone
      have hrightLength : rhs.val.length = 1 := hlen.symm.trans hleftLength
      step -grind with (Aeneas.Std.Slice.index_usize_spec lhs 0#usize (by scalar_tac)) as ⟨a,haIndex⟩
      step -grind with (Aeneas.Std.Slice.index_usize_spec rhs 0#usize (by scalar_tac)) as ⟨b,hbIndex⟩
      obtain ⟨x,hx⟩ := List.length_eq_one_iff.mp hleftLength
      obtain ⟨y,hy⟩ := List.length_eq_one_iff.mp hrightLength
      have hax : a = x := by simpa [hx] using haIndex
      have hby : b = y := by simpa [hy] using hbIndex
      have hamem : a ∈ lhs.val := by simp [hx, hax]
      have hbmem : b ∈ rhs.val := by simp [hy, hby]
      have hraw : rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val =
          val4 a.limbs * val4 b.limbs := by simp [hx, hy, hax, hby, rawSum]
      apply WP.spec_mono (portable_multiply_spec (portableDict inst) params a b (haLoose a hamem) (hbLoose b hbmem))
      intro out hout
      exact ⟨hout.1, by simpa only [hraw] using hout.2⟩
    · rw [if_neg hone]
      simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.zip.trait_default,
        core.iter.traits.iterator.Iterator.zip.default,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
      step -grind with (slice_accumulation_spec lhs rhs hlen hwideBound) as ⟨wide,hwide⟩
      simp only [hs, ht, bind_ok]
      have hscaled : val8 wide < (stateWeight s * stateWeight t) * val4 params.modulus * R := by
        rw [hwide]
        exact short_sum_scaled_bound (fun a => val4 a.limbs) (fun b => val4 b.limbs)
          (val4 params.modulus) params.positive params.thrice_lt s t lhs.val rhs.val hlen hshort ha hb
      have hfinal : finish inst s t wide ⦃ out =>
          val4 out.limbs < 2 * val4 params.modulus ∧
          Nat.ModEq (val4 params.modulus) (R * val4 out.limbs)
            (rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val) ⦄ := by
        apply WP.spec_mono (finish_spec inst params s t wide hscaled)
        intro out hout
        exact ⟨hout.1, by simpa only [hwide] using hout.2⟩
      cases s <;> cases t <;> simpa [finish] using hfinal

#print axioms state_weight_le_two
#print axioms slice_short_spec
end UdonVerify.ProductPortable
