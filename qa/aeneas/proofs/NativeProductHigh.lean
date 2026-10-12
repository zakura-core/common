import NativeProductTerm
import ReduceProofs

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def productLow (wide : A8) : A4 :=
  Array.make 4#usize [wide[0]!, wide[1]!, wide[2]!, wide[3]!]

def productHigh (wide : A8) : A4 :=
  Array.make 4#usize [wide[4]!, wide[5]!, wide[6]!, wide[7]!]

theorem product_halves_value (wide : A8) :
    val8 wide = val4 (productLow wide) + R * val4 (productHigh wide) := by
  simp [productLow, productHigh, val4, val8, R]
  ring

/-- Reducing the high half preserves the wide integer modulo the prime. -/
@[step]
theorem product_fold_high_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (wide : A8) (twice : Bool)
    (hhigh : val4 (productHigh wide) < (if twice then 4 else 2) * val4 params.modulus) :
    NativeField.zakura_udon.field.pasta.products.fold_high inst wide twice
      ⦃ out => val8 out < val4 params.modulus * R ∧
        Nat.ModEq (val4 params.modulus) (val8 out) (val8 wide) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.fold_high
  step +scalarTac -grind as ⟨word4, hword4⟩
  step +scalarTac -grind as ⟨word5, hword5⟩
  step +scalarTac -grind as ⟨word6, hword6⟩
  step +scalarTac -grind as ⟨word7, hword7⟩
  let high : A4 := Array.make 4#usize [word4, word5, word6, word7]
  have hhighValue : val4 high = val4 (productHigh wide) := by
    simp_all [high, productHigh, val4]
  have hmiddle : (if twice then
      NativeField.zakura_udon.field.pasta.montgomery.reduce_twice_modulus inst high 0#u64
    else ok high) ⦃ out => val4 out < 2 * val4 params.modulus ∧
      Nat.ModEq (val4 params.modulus) (val4 out) (val4 high) ⦄ := by
    cases twice with
    | false =>
      rw [if_neg (by decide : ¬ ((false : Bool) = true))]
      simp only [WP.spec_ok]
      exact ⟨by simpa [hhighValue] using hhigh, Nat.ModEq.refl _⟩
    | true =>
      rw [if_pos (show (true : Bool) = true from rfl)]
      rw [reduce_twice_eq]
      have hbound : val4 high + R * (0#u64).val < 4 * val4 params.modulus := by
        simpa [hhighValue] using hhigh
      step -grind with (reduce_twice_modulus_spec (kernelInst inst) params high 0#u64 hbound)
        as ⟨out, hvalue, hbound⟩
      refine ⟨hbound, ?_⟩
      have hvalueHigh : val4 out = val4 high % (2 * val4 params.modulus) := by
        simpa only [mul_zero, add_zero] using hvalue
      have hmod : Nat.ModEq (2 * val4 params.modulus) (val4 out) (val4 high) := by
        simp only [Nat.ModEq, hvalueHigh, Nat.mod_mod]
      exact hmod.of_dvd (dvd_mul_left (val4 params.modulus) 2)
  step -grind with hmiddle as ⟨middle, hbound, hmod⟩
  change Nat.ModEq (val4 params.modulus) (val4 middle) (val4 high) at hmod
  rw [reduce_once_eq]
  step -grind with (reduce_once_spec (kernelInst inst) params middle hbound)
    as ⟨reduced, hreduced, hreducedBound⟩
  have hreducedMod : Nat.ModEq (val4 params.modulus) (val4 reduced)
      (val4 (productHigh wide)) := by
    have hfirst : Nat.ModEq (val4 params.modulus) (val4 reduced) (val4 middle) := by
      simp only [Nat.ModEq, hreduced, Nat.mod_mod]
    simpa only [hhighValue] using hfirst.trans hmod
  step -grind with (Array.index_mut_SliceIndexRangeFromUsizeSlice wide
    { start := 4#usize } (by decide)) as ⟨targetSlice, back, htarget, hlength, hback⟩
  step -grind as ⟨sourceSlice, hsource⟩
  have hlengths : targetSlice.length = sourceSlice.length := by
    rw [hsource]
    simp [Array.to_slice] at hlength ⊢
    omega
  step -grind with (core.slice.Slice.copy_from_slice.step_spec
    core.marker.CopyU64 targetSlice sourceSlice hlengths) as ⟨copied, hcopied⟩
  subst copied
  try simp only [WP.spec_ok]
  have hvalues : (back sourceSlice).val = wide.val.setSlice! 4 reduced.val := by
    rw [hback sourceSlice, hsource]
    simp [Array.to_slice]
  have houtput : val8 (back sourceSlice) = val4 (productLow wide) + R * val4 reduced := by
    simpa [productLow, val4] using upper_splice_value wide reduced (back sourceSlice) hvalues
  rw [houtput]
  refine ⟨?_, ?_⟩
  · have hlow := val4_lt (productLow wide)
    have hround : val4 reduced + 1 ≤ val4 params.modulus := by omega
    nlinarith only [hlow, hround]
  · rw [product_halves_value]
    exact (hreducedMod.mul_left R).add_left (val4 (productLow wide))

#print axioms product_halves_value
#print axioms product_fold_high_spec

end UdonVerify.Native
