import NativeProductStates

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def productScale (double : Bool) : Nat := if double then 2 else 1

def productOffsetScale (reduced double : Bool) : Nat :=
  if reduced then 1 else if double then 3 else 2

def productOffset {M : Type} (inst : Modulus M) (reduced double : Bool) : Result A4 := do
  if reduced then inst.MODULUS
  else if double then
    let modulus ← inst.MODULUS
    let twice ← inst.sealedParametersInst.TWICE_MODULUS
    let (offset, _) ← NativeField.zakura_udon.field.pasta.word.add_limbs twice modulus
    ok offset
  else inst.sealedParametersInst.TWICE_MODULUS

/-- The three selected offsets are the actual modulus, twice modulus, or their checked sum. -/
@[step]
theorem product_offset_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (reduced double : Bool) :
    productOffset inst reduced double
      ⦃ offset => val4 offset = productOffsetScale reduced double * val4 params.modulus ⦄ := by
  have hm : inst.MODULUS = ok params.modulus := params.modulus_ok
  have ht : inst.sealedParametersInst.TWICE_MODULUS = ok params.twice := params.twice_ok
  cases reduced <;> cases double <;>
    simp only [productOffset, productOffsetScale, Bool.false_eq_true, if_false, if_true,
      hm, ht, bind_ok, one_mul]
  · simpa only [WP.spec_ok] using params.twice_val
  · rw [add_limbs_eq]
    step -grind with (slice_add_limbs_spec params.twice params.modulus)
      as ⟨offset, carry, hcarry, hsum⟩
    try simp only [WP.spec_ok]
    rw [params.twice_val] at hsum
    have hthrice := params.thrice_lt
    have hzero : carry.val = 0 := by
      norm_num [B, R] at hsum hthrice
      omega
    simp only [hzero, mul_zero, add_zero] at hsum
    omega
  · simp only [WP.spec_ok]
  · simp only [WP.spec_ok]

theorem product_reduced_flags {S T U V : Type}
    (si : ProductState S) (ti : ProductState T) (ui : ProductState U) (vi : ProductState V)
    (ss : ProductRepresentation si) (ts : ProductRepresentation ti)
    (us : ProductRepresentation ui) (vs : ProductRepresentation vi) :
    (do
      let b ← si.sealedSealedInst.REDUCED
      if b then
        let b1 ← ti.sealedSealedInst.REDUCED
        if b1 then
          let b2 ← ui.sealedSealedInst.REDUCED
          if b2 then vi.sealedSealedInst.REDUCED else ok false
        else ok false
      else ok false) = ok (ss.reduced && ts.reduced && us.reduced && vs.reduced) := by
  rw [ss.reduced_ok, ts.reduced_ok, us.reduced_ok, vs.reduced_ok]
  cases ss.reduced <;> cases ts.reduced <;> cases us.reduced <;> cases vs.reduced <;>
    simp [bind_ok]

theorem product_pair_value_bounds (p a b : Nat) (hp : 0 < p)
    (sa sb : Bool) (ha : a < if sa then p else 2 * p)
    (hb : b < if sb then p else 2 * p) : a * b < 4 * p ^ 2 := by
  have ha' : a < 2 * p := by split at ha <;> omega
  have hb' : b < 2 * p := by split at hb <;> omega
  have h := product_lt_square_bound (2 * p) a b (by omega) ha' hb'
  nlinarith only [h]

/-- Operand states imply the exact input limits needed by the restoration offset. -/
theorem product_difference_input_bounds {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (a b c d : Nat)
    (sa sb sc sd double : Bool)
    (ha : a < if sa then val4 params.modulus else 2 * val4 params.modulus)
    (hb : b < if sb then val4 params.modulus else 2 * val4 params.modulus)
    (hc : c < if sc then val4 params.modulus else 2 * val4 params.modulus)
    (hd : d < if sd then val4 params.modulus else 2 * val4 params.modulus) :
    a * b < R * (productOffsetScale (sa && sb && sc && sd) double * val4 params.modulus) ∧
      productScale double * (c * d) <
        R * (productOffsetScale (sa && sb && sc && sd) double * val4 params.modulus) := by
  have hab := product_pair_value_bounds _ a b params.positive sa sb ha hb
  have hcd := product_pair_value_bounds _ c d params.positive sc sd hc hd
  by_cases hreduced : (sa && sb && sc && sd) = true
  · have hstates := hreduced
    simp only [Bool.and_eq_true] at hstates
    obtain ⟨⟨⟨hs, ht⟩, hu⟩, hv⟩ := hstates
    simp only [hs, ht, hu, hv, if_true] at ha hb hc hd
    have hab' := product_lt_square_bound _ a b params.positive ha hb
    have hcd' := product_lt_square_bound _ c d params.positive hc hd
    simpa only [productOffsetScale, productScale, hreduced, if_true, one_mul] using
      product_reduced_offset_bound inst params (a * b) (c * d) hab' hcd' double
  · simpa only [productOffsetScale, productScale, hreduced, Bool.false_eq_true, if_false] using
      product_loose_offset_bound inst params (a * b) (c * d) hab hcd double

#print axioms product_offset_spec
#print axioms product_reduced_flags
#print axioms product_pair_value_bounds
#print axioms product_difference_input_bounds

end UdonVerify.Native
