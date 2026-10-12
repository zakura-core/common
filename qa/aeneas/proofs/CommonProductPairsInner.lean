import CommonProductPairsFold

open Aeneas Std Result

namespace UdonVerify.ProductPairs
open UdonVerify.Native UdonVerify.ProductPortable
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Each product is accumulated exactly until a possible ninth-word overflow is folded. -/
@[step]
theorem pairs_inner_spec {M S T : Type} (bounded : Bool) (inst : Native.Modulus M)
    (params : PastaParameters (Native.kernelInst inst)) (constants : Native.WideFieldParameters inst params)
    (sum : ProductPortable.Sum M) (lhs : ProductPortable.Element M S) (rhs : ProductPortable.Element M T)
    (hbound : bounded = true → sumInteger sum + val4 lhs.limbs * val4 rhs.limbs < B ^ 9) :
    CommonProductPairs.field.pasta.products.ProductSum.add_product_inner
      bounded (portableDict inst) sum lhs rhs
      ⦃ out => Nat.ModEq (val4 params.modulus) (sumInteger out)
          (sumInteger sum + val4 lhs.limbs * val4 rhs.limbs) ∧
        (bounded = true → sumInteger out = sumInteger sum + val4 lhs.limbs * val4 rhs.limbs) ⦄ := by
  unfold CommonProductPairs.field.pasta.products.ProductSum.add_product_inner
  simp only [PortableBridge.field.pasta.word.mac, portable_mac_bridge,
    PortableBridge.field.pasta.word.adc, portable_adc_bridge]
  step +scalarTac -grind as ⟨wide0, hwide0⟩
  step +scalarTac -grind as ⟨lhs0, hlhs0⟩
  step +scalarTac -grind as ⟨rhs0, hrhs0⟩
  obtain ⟨digit00, carry00, hresult00, hvalue00⟩ :=
    product_mac_result wide0 lhs0 rhs0 0#u64
  rw [hresult00]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨wide1, hwide1⟩
  step +scalarTac -grind as ⟨rhs1, hrhs1⟩
  obtain ⟨digit01, carry01, hresult01, hvalue01⟩ :=
    product_mac_result wide1 lhs0 rhs1 carry00
  rw [hresult01]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨wide2, hwide2⟩
  step +scalarTac -grind as ⟨rhs2, hrhs2⟩
  obtain ⟨digit02, carry02, hresult02, hvalue02⟩ :=
    product_mac_result wide2 lhs0 rhs2 carry01
  rw [hresult02]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨wide3, hwide3⟩
  step +scalarTac -grind as ⟨rhs3, hrhs3⟩
  obtain ⟨digit03, carry03, hresult03, hvalue03⟩ :=
    product_mac_result wide3 lhs0 rhs3 carry02
  rw [hresult03]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨wide4, hwide4⟩
  obtain ⟨top0, overflow0, htopResult0, htopValue0⟩ :=
    product_adc_result wide4 carry03 0#u64
  rw [htopResult0]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨lhs1, hlhs1⟩
  obtain ⟨digit10, carry10, hresult10, hvalue10⟩ :=
    product_mac_result digit01 lhs1 rhs0 0#u64
  rw [hresult10]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit11, carry11, hresult11, hvalue11⟩ :=
    product_mac_result digit02 lhs1 rhs1 carry10
  rw [hresult11]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit12, carry12, hresult12, hvalue12⟩ :=
    product_mac_result digit03 lhs1 rhs2 carry11
  rw [hresult12]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit13, carry13, hresult13, hvalue13⟩ :=
    product_mac_result top0 lhs1 rhs3 carry12
  rw [hresult13]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨wide5, hwide5⟩
  obtain ⟨top1, overflow1, htopResult1, htopValue1⟩ :=
    product_adc_result wide5 carry13 overflow0
  rw [htopResult1]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨lhs2, hlhs2⟩
  obtain ⟨digit20, carry20, hresult20, hvalue20⟩ :=
    product_mac_result digit11 lhs2 rhs0 0#u64
  rw [hresult20]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit21, carry21, hresult21, hvalue21⟩ :=
    product_mac_result digit12 lhs2 rhs1 carry20
  rw [hresult21]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit22, carry22, hresult22, hvalue22⟩ :=
    product_mac_result digit13 lhs2 rhs2 carry21
  rw [hresult22]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit23, carry23, hresult23, hvalue23⟩ :=
    product_mac_result top1 lhs2 rhs3 carry22
  rw [hresult23]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨wide6, hwide6⟩
  obtain ⟨top2, overflow2, htopResult2, htopValue2⟩ :=
    product_adc_result wide6 carry23 overflow1
  rw [htopResult2]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨lhs3, hlhs3⟩
  obtain ⟨digit30, carry30, hresult30, hvalue30⟩ :=
    product_mac_result digit21 lhs3 rhs0 0#u64
  rw [hresult30]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit31, carry31, hresult31, hvalue31⟩ :=
    product_mac_result digit22 lhs3 rhs1 carry30
  rw [hresult31]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit32, carry32, hresult32, hvalue32⟩ :=
    product_mac_result digit23 lhs3 rhs2 carry31
  rw [hresult32]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨digit33, carry33, hresult33, hvalue33⟩ :=
    product_mac_result top2 lhs3 rhs3 carry32
  rw [hresult33]
  simp only [bind_ok, Std.uncurry]
  step +scalarTac -grind as ⟨wide7, hwide7⟩
  obtain ⟨top3, overflow3, htopResult3, htopValue3⟩ :=
    product_adc_result wide7 carry33 overflow2
  rw [htopResult3]
  simp only [bind_ok, Std.uncurry]
  obtain ⟨sumCarry, sumOverflow, hcarryResult, hcarryValue⟩ :=
    product_adc_result sum.carry overflow3 0#u64
  rw [hcarryResult]
  simp only [bind_ok, Std.uncurry]
  let raw : ProductPortable.Sum M := { sum with
    wide := Array.make 8#usize [digit00, digit10, digit20, digit30, digit31, digit32, digit33, top3], carry := sumCarry }
  have hraw : sumInteger raw + B ^ 9 * sumOverflow.val =
      sumInteger sum + val4 lhs.limbs * val4 rhs.limbs := by
    simp_all [raw, ProductPortable.sumInteger, sumToNative, Native.sumInteger, accumulatorValue, val4, val8]
    norm_num [B, R] at *
    ring_nf at *
    omega
  have hoverflow : sumOverflow.val ≤ 1 :=
    adc_carry_le_one sum.carry overflow3 0#u64 sumCarry sumOverflow (by decide) hcarryValue
  cases bounded with
  | false =>
    step -grind
    simp only [Bool.false_eq_true, if_false]
    step -grind with (pairs_fold_overflow_spec inst params constants raw sumOverflow hoverflow)
      as ⟨out, hout⟩
    refine ⟨?_, by simp⟩
    change Nat.ModEq (val4 params.modulus) (sumInteger out)
      (sumInteger raw + B ^ 9 * sumOverflow.val) at hout
    rw [hraw] at hout
    exact hout
  | true =>
    have hzeroVal : sumOverflow.val = 0 := by
      have htotal := hbound rfl
      norm_num [B] at hraw htotal
      omega
    have hzero : sumOverflow = 0#u64 := by scalar_tac
    subst sumOverflow
    step -grind
    simp only [if_true, WP.spec_ok]
    have hexact : sumInteger raw = sumInteger sum + val4 lhs.limbs * val4 rhs.limbs := by
      simpa using hraw
    refine ⟨?_, hexact⟩
    change Nat.ModEq (val4 params.modulus) (sumInteger raw)
      (sumInteger sum + val4 lhs.limbs * val4 rhs.limbs)
    rw [hexact]

#print axioms pairs_inner_spec

end UdonVerify.ProductPairs
