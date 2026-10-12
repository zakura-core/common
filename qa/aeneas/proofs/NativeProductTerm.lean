import NativeProductFold

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem upper_splice_value (wide : A8) (tail : A4) (out : A8)
    (hvalues : out.val = wide.val.setSlice! 4 tail.val) :
    val8 out = wide[0]!.val + B * wide[1]!.val + B ^ 2 * wide[2]!.val +
      B ^ 3 * wide[3]!.val + R * val4 tail := by
  have hlow (j : Nat) (hj : j < 4) : out[j]! = wide[j]! := by
    simp only [Array.getElem!_Nat_eq, hvalues]
    exact List.getElem!_setSlice!_prefix _ _ _ _ hj
  have hhigh (j : Nat) (hj : j < 4) : out[j + 4]! = tail[j]! := by
    simp only [Array.getElem!_Nat_eq, hvalues]
    simpa using List.getElem!_setSlice!_middle wide.val tail.val 4 (j + 4)
      (by simp only [Array.property]; norm_num; omega)
  simp only [val8, val4, hlow 0 (by decide), hlow 1 (by decide), hlow 2 (by decide),
    hlow 3 (by decide), hhigh 0 (by decide), hhigh 1 (by decide), hhigh 2 (by decide),
    hhigh 3 (by decide)]
  norm_num only [R]
  ring

/-- A single stored field value is inserted at weight R before final reduction. -/
@[step]
theorem product_add_term_spec {M S : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (sum : Sum M) (term : Element M S) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.add_term inst sum term
      ⦃ out => Nat.ModEq (val4 params.modulus) (sumInteger out)
        (sumInteger sum + R * val4 term.limbs) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.ProductSum.add_term
  step +scalarTac -grind as ⟨wide0, hwide0⟩
  step +scalarTac -grind as ⟨term0, hterm0⟩
  obtain ⟨digit0, carry0, hresult0, hsum0⟩ := product_adc_result wide0 term0 0#u64
  rw [hresult0]
  simp only [bind_ok, Std.uncurry]
  have hcarry0 : carry0.val ≤ 1 :=
    adc_carry_le_one wide0 term0 0#u64 digit0 carry0 (by decide) hsum0
  step +scalarTac -grind as ⟨wide1, hwide1⟩
  step +scalarTac -grind as ⟨term1, hterm1⟩
  obtain ⟨digit1, carry1, hresult1, hsum1⟩ := product_adc_result wide1 term1 carry0
  rw [hresult1]
  simp only [bind_ok, Std.uncurry]
  have hcarry1 : carry1.val ≤ 1 :=
    adc_carry_le_one wide1 term1 carry0 digit1 carry1 hcarry0 hsum1
  step +scalarTac -grind as ⟨wide2, hwide2⟩
  step +scalarTac -grind as ⟨term2, hterm2⟩
  obtain ⟨digit2, carry2, hresult2, hsum2⟩ := product_adc_result wide2 term2 carry1
  rw [hresult2]
  simp only [bind_ok, Std.uncurry]
  have hcarry2 : carry2.val ≤ 1 :=
    adc_carry_le_one wide2 term2 carry1 digit2 carry2 hcarry1 hsum2
  step +scalarTac -grind as ⟨wide3, hwide3⟩
  step +scalarTac -grind as ⟨term3, hterm3⟩
  obtain ⟨digit3, carry3, hresult3, hsum3⟩ := product_adc_result wide3 term3 carry2
  rw [hresult3]
  simp only [bind_ok, Std.uncurry]
  have hcarry3 : carry3.val ≤ 1 :=
    adc_carry_le_one wide3 term3 carry2 digit3 carry3 hcarry2 hsum3
  obtain ⟨sumCarry, overflow, hresultCarry, hsumCarry⟩ := product_adc_result sum.carry 0#u64 carry3
  rw [hresultCarry]
  simp only [bind_ok, Std.uncurry]
  have hoverflow : overflow.val ≤ 1 :=
    adc_carry_le_one sum.carry 0#u64 carry3 sumCarry overflow hcarry3 hsumCarry
  step -grind with (Array.index_mut_SliceIndexRangeFromUsizeSlice sum.wide
    { start := 4#usize } (by decide)) as ⟨targetSlice, back, htarget, hlength, hback⟩
  step -grind as ⟨sourceSlice, hsource⟩
  have hlengths : targetSlice.length = sourceSlice.length := by
    rw [hsource]
    simp [Array.to_slice] at hlength ⊢
    omega
  step -grind with (core.slice.Slice.copy_from_slice.step_spec
    core.marker.CopyU64 targetSlice sourceSlice hlengths) as ⟨copied, hcopied⟩
  subst copied
  let tail : A4 := Array.make 4#usize [digit0, digit1, digit2, digit3]
  have hvalues : (back sourceSlice).val = sum.wide.val.setSlice! 4 tail.val := by
    rw [hback sourceSlice, hsource]
    simp [tail, Array.to_slice]
  have hwideValue := upper_splice_value sum.wide tail (back sourceSlice) hvalues
  let raw : Sum M := { sum with wide := back sourceSlice, carry := sumCarry }
  have hraw : sumInteger raw + B ^ 9 * overflow.val =
      sumInteger sum + R * val4 term.limbs := by
    simp only [raw, sumInteger, accumulatorValue]
    rw [hwideValue]
    simp_all [tail, val4, val8]
    norm_num [B, R] at *
    ring_nf at *
    omega
  step -grind with (product_fold_overflow_spec inst params constants raw overflow hoverflow)
    as ⟨out, hout⟩
  change Nat.ModEq (val4 params.modulus) (sumInteger out)
    (sumInteger raw + B ^ 9 * overflow.val) at hout
  rw [hraw] at hout
  exact hout

#print axioms upper_splice_value
#print axioms product_add_term_spec

end UdonVerify.Native
