import NativeProductLimits
import NativeProductRestoreLoop

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

abbrev ProductState := NativeField.zakura_udon.field.pasta.representation.ReductionState

structure ProductRepresentation {S : Type} (inst : ProductState S) where
  reduced : Bool
  reduced_ok : inst.sealedSealedInst.REDUCED = ok reduced

def productRepresentationBound {S : Type} {inst : ProductState S}
    (p : Nat) (state : ProductRepresentation inst) : Nat :=
  if state.reduced then p else 2 * p

def productLooseRepresentation : ProductRepresentation looseInst where
  reduced := false
  reduced_ok := by with_unfolding_all rfl

def productReducedRepresentation : ProductRepresentation reducedInst where
  reduced := true
  reduced_ok := by with_unfolding_all rfl

theorem product_representation_loose_bound {S : Type} {inst : ProductState S}
    (p : Nat) (state : ProductRepresentation inst) (value : Nat)
    (hvalue : value < productRepresentationBound p state) : value < 2 * p := by
  unfold productRepresentationBound at hvalue
  split at hvalue <;> omega

theorem product_wrapping_mask (borrow : U64) (hborrow : borrow.val ≤ 1) :
    core.num.U64.wrapping_sub 0#u64 borrow =
      if borrow.val = 0 then 0#u64 else fullMask := by
  have hcases : borrow = 0#u64 ∨ borrow = 1#u64 := by scalar_tac
  rcases hcases with hzero | hone <;> subst borrow <;> rfl

theorem product_masked_offset (offset : A4) (borrow : U64) (hborrow : borrow.val ≤ 1) :
    val4 (maskWords offset (core.num.U64.wrapping_sub 0#u64 borrow)) =
      val4 offset * borrow.val := by
  rw [product_wrapping_mask borrow hborrow]
  by_cases hz : borrow.val = 0
  · simp only [hz, if_true, mask_words_zero, mul_zero]
  · have hone : borrow.val = 1 := by omega
    simpa [hone] using mask_words_full offset

theorem product_second_subtract_eq (it : WideZip) (back : WideZip → WideZip) (borrow : U64) :
    NativeField.zakura_udon.field.pasta.products.PastaField.product_difference_loop3 it back borrow =
      NativeField.zakura_udon.field.pasta.products.PastaField.product_difference_loop1 it back borrow := by rfl

theorem product_second_restore_eq (it : RestoreZip) (back : RestoreZip → RestoreZip) (mask carry : U64) :
    NativeField.zakura_udon.field.pasta.products.PastaField.product_difference_loop4 it back mask carry =
      NativeField.zakura_udon.field.pasta.products.PastaField.product_difference_loop2 it back mask carry := by rfl

/-- Loose products and their doubled forms fit the offsets selected by the Rust routine. -/
theorem product_loose_offset_bound {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (left right : Nat)
    (hleft : left < 4 * val4 params.modulus ^ 2)
    (hright : right < 4 * val4 params.modulus ^ 2) (double : Bool) :
    left < R * ((if double then 3 else 2) * val4 params.modulus) ∧
      (if double then 2 else 1) * right <
        R * ((if double then 3 else 2) * val4 params.modulus) := by
  have hp := params.positive
  have hthrice := params.thrice_lt
  have htwice : 2 * val4 params.modulus < R := by omega
  have htwo := Nat.mul_lt_mul_of_pos_right htwice (show 0 < 2 * val4 params.modulus by omega)
  have hthree := Nat.mul_lt_mul_of_pos_right hthrice (show 0 < 8 * val4 params.modulus by omega)
  cases double <;> try simp only [Bool.false_eq_true, if_true, if_false, one_mul]
  · constructor <;> nlinarith only [hleft, hright, htwo]
  · constructor <;> nlinarith only [hleft, hright, hthree]

theorem product_reduced_offset_bound {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (left right : Nat)
    (hleft : left < val4 params.modulus ^ 2)
    (hright : right < val4 params.modulus ^ 2) (double : Bool) :
    left < R * val4 params.modulus ∧
      (if double then 2 else 1) * right < R * val4 params.modulus := by
  have htwice : 2 * val4 params.modulus < R := by have h := params.thrice_lt; omega
  have hmul := Nat.mul_lt_mul_of_pos_right htwice params.positive
  cases double <;> try simp only [Bool.false_eq_true, if_true, if_false, one_mul]
  all_goals constructor <;> nlinarith only [hleft, hright, hmul]

#print axioms productLooseRepresentation
#print axioms productReducedRepresentation
#print axioms product_representation_loose_bound
#print axioms product_wrapping_mask
#print axioms product_masked_offset
#print axioms product_second_subtract_eq
#print axioms product_second_restore_eq
#print axioms product_loose_offset_bound
#print axioms product_reduced_offset_bound

end UdonVerify.Native
