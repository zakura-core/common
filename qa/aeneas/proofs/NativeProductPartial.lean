import NativeProductWords

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Folding the highest two accumulator words preserves its integer modulo the prime. -/
@[step]
theorem product_partial_reduce_spec {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (constants : WideFieldParameters inst params)
    (sum : Sum M) :
    NativeField.zakura_udon.field.pasta.products.ProductSum.partial_reduce inst sum
      ⦃ out => val8 out < 2 * B ^ 7 ∧ val8 out < val4 params.modulus * R ∧
        Nat.ModEq (val4 params.modulus) (val8 out) (sumInteger sum) ⦄ := by
  unfold NativeField.zakura_udon.field.pasta.products.ProductSum.partial_reduce
  step +scalarTac -grind as ⟨upper, hupper⟩
  rw [constants.high448_ok]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨coef00, hcoef00⟩
  obtain ⟨t00, carry00, hresult00, hvalue00⟩ :=
    product_mac_result 0#u64 upper coef00 0#u64
  rw [hresult00]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨coef01, hcoef01⟩
  obtain ⟨t01, carry01, hresult01, hvalue01⟩ :=
    product_mac_result 0#u64 upper coef01 carry00
  rw [hresult01]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨coef02, hcoef02⟩
  obtain ⟨t02, carry02, hresult02, hvalue02⟩ :=
    product_mac_result 0#u64 upper coef02 carry01
  rw [hresult02]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨coef03, hcoef03⟩
  obtain ⟨t03, carry03, hresult03, hvalue03⟩ :=
    product_mac_result 0#u64 upper coef03 carry02
  rw [hresult03]
  simp only [bind_ok, Std.uncurry]
  rw [constants.conversion.radix2_ok]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨coef10, hcoef10⟩
  obtain ⟨t10, carry10, hresult10, hvalue10⟩ :=
    product_mac_result t00 sum.carry coef10 0#u64
  rw [hresult10]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨coef11, hcoef11⟩
  obtain ⟨t11, carry11, hresult11, hvalue11⟩ :=
    product_mac_result t01 sum.carry coef11 carry10
  rw [hresult11]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨coef12, hcoef12⟩
  obtain ⟨t12, carry12, hresult12, hvalue12⟩ :=
    product_mac_result t02 sum.carry coef12 carry11
  rw [hresult12]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨coef13, hcoef13⟩
  obtain ⟨t13, carry13, hresult13, hvalue13⟩ :=
    product_mac_result t03 sum.carry coef13 carry12
  rw [hresult13]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨t4, overflow, ht4, htop⟩ := product_adc_result carry03 0#u64 carry13
  rw [ht4]
  simp only [bind_ok, Std.uncurry]
  have hcoefficient : t10.val + B * t11.val + B ^ 2 * t12.val + B ^ 3 * t13.val +
      B ^ 4 * t4.val + B ^ 5 * overflow.val =
      upper.val * val4 constants.high448 + sum.carry.val * val4 constants.conversion.radix2 := by
    simp_all [val4]
    norm_num [B] at *
    ring_nf at *
    omega
  have h448 : val4 constants.high448 < val4 params.modulus := by
    rw [constants.high448_val]
    exact Nat.mod_lt _ params.positive
  have hr2 : val4 constants.conversion.radix2 < val4 params.modulus := by
    rw [constants.conversion.radix2_val]
    exact Nat.mod_lt _ params.positive
  have hcoefficientBound := partial_coefficient_bound inst params upper sum.carry
    constants.high448 constants.conversion.radix2 h448 hr2
  have hzero : overflow.val = 0 := by
    norm_num [B] at hcoefficient hcoefficientBound
    omega
  have hzeroScalar : overflow = 0#u64 := by norm_num only [B]; scalar_tac
  subst overflow
  have hcoefficientExact : t10.val + B * t11.val + B ^ 2 * t12.val + B ^ 3 * t13.val +
      B ^ 4 * t4.val = upper.val * val4 constants.high448 +
        sum.carry.val * val4 constants.conversion.radix2 := by
    simpa using hcoefficient
  step -grind
  step +scalarTac -grind as ⟨word0, hword0⟩
  obtain ⟨d0, finalCarry0, hresultSum0, hsum0⟩ :=
    product_adc_result word0 t10 0#u64
  rw [hresultSum0]
  simp only [bind_ok, Std.uncurry]
  have hcarry0 : finalCarry0.val ≤ 1 :=
    adc_carry_le_one word0 t10 0#u64 d0 finalCarry0 (by decide) hsum0
  step +scalarTac -grind as ⟨word1, hword1⟩
  obtain ⟨d1, finalCarry1, hresultSum1, hsum1⟩ :=
    product_adc_result word1 t11 finalCarry0
  rw [hresultSum1]
  simp only [bind_ok, Std.uncurry]
  have hcarry1 : finalCarry1.val ≤ 1 :=
    adc_carry_le_one word1 t11 finalCarry0 d1 finalCarry1 hcarry0 hsum1
  step +scalarTac -grind as ⟨word2, hword2⟩
  obtain ⟨d2, finalCarry2, hresultSum2, hsum2⟩ :=
    product_adc_result word2 t12 finalCarry1
  rw [hresultSum2]
  simp only [bind_ok, Std.uncurry]
  have hcarry2 : finalCarry2.val ≤ 1 :=
    adc_carry_le_one word2 t12 finalCarry1 d2 finalCarry2 hcarry1 hsum2
  step +scalarTac -grind as ⟨word3, hword3⟩
  obtain ⟨d3, finalCarry3, hresultSum3, hsum3⟩ :=
    product_adc_result word3 t13 finalCarry2
  rw [hresultSum3]
  simp only [bind_ok, Std.uncurry]
  have hcarry3 : finalCarry3.val ≤ 1 :=
    adc_carry_le_one word3 t13 finalCarry2 d3 finalCarry3 hcarry2 hsum3
  step +scalarTac -grind as ⟨word4, hword4⟩
  obtain ⟨d4, finalCarry4, hresultSum4, hsum4⟩ :=
    product_adc_result word4 t4 finalCarry3
  rw [hresultSum4]
  simp only [bind_ok, Std.uncurry]
  have hcarry4 : finalCarry4.val ≤ 1 :=
    adc_carry_le_one word4 t4 finalCarry3 d4 finalCarry4 hcarry3 hsum4
  step +scalarTac -grind as ⟨word5, hword5⟩
  obtain ⟨d5, finalCarry5, hresultSum5, hsum5⟩ :=
    product_adc_result word5 0#u64 finalCarry4
  rw [hresultSum5]
  simp only [bind_ok, Std.uncurry]
  have hcarry5 : finalCarry5.val ≤ 1 :=
    adc_carry_le_one word5 0#u64 finalCarry4 d5 finalCarry5 hcarry4 hsum5
  step +scalarTac -grind as ⟨word6, hword6⟩
  obtain ⟨d6, finalCarry6, hresultSum6, hsum6⟩ :=
    product_adc_result word6 0#u64 finalCarry5
  rw [hresultSum6]
  simp only [bind_ok, Std.uncurry]
  have hcarry6 : finalCarry6.val ≤ 1 :=
    adc_carry_le_one word6 0#u64 finalCarry5 d6 finalCarry6 hcarry5 hsum6
  step +scalarTac -grind
  have hout : val8 (Array.make 8#usize [d0, d1, d2, d3, d4, d5, d6, finalCarry6]) =
      val7 sum.wide + sum.wide[7]!.val * val4 constants.high448 +
        sum.carry.val * val4 constants.conversion.radix2 := by
    simp_all [val8, val7]
    norm_num [B] at *
    ring_nf at *
    omega
  rw [hout]
  have hupperBound : sum.wide[7]!.val < B := by norm_num only [B]; scalar_tac
  have hcarryBound : sum.carry.val < B := by norm_num only [B]; scalar_tac
  have hb := partial_reduce_bound inst params (val7 sum.wide) sum.wide[7]!.val
    sum.carry.val (val4 constants.high448) (val4 constants.conversion.radix2)
    (val7_lt _) hupperBound hcarryBound h448 hr2
  refine ⟨hb.1, hb.2, ?_⟩
  have h448mod : Nat.ModEq (val4 params.modulus) (val4 constants.high448) (B ^ 7) := by
    simp only [Nat.ModEq, constants.high448_val, Nat.mod_mod]
  have hr2mod : Nat.ModEq (val4 params.modulus) (val4 constants.conversion.radix2) (R ^ 2) := by
    simp only [Nat.ModEq, constants.conversion.radix2_val, Nat.mod_mod]
  simpa only [sumInteger, accumulatorValue, val8_split] using
    partial_reduce_congruence (val4 params.modulus) (val7 sum.wide) sum.wide[7]!.val
      sum.carry.val (val4 constants.high448) (val4 constants.conversion.radix2) h448mod hr2mod

#print axioms product_partial_reduce_spec

end UdonVerify.Native
