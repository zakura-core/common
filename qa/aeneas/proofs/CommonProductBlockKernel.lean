import CommonProductBlockCore

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.ProductAarch64 UdonVerify.CommonComba UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev initialColumns (word : U64) : BatchColumns :=
  Array.make 4#usize [Array.make 3#usize [word,0#u64,0#u64],
    Array.repeat 3#usize 0#u64,Array.repeat 3#usize 0#u64,Array.repeat 3#usize 0#u64]

theorem initial_columns_value (word : U64) :
    batchColumnsInteger (initialColumns word) = word.val := by
  simp [initialColumns,batchColumnsInteger,batchColumnInteger]

theorem initial_columns_bound (word : U64) :
    batchColumnsInteger (initialColumns word) < 2 * B ^ 2 := by
  rw [initial_columns_value]
  have h := word.hmax
  norm_num [UScalar.max,UScalarTy.U64_numBits_eq,B] at *
  omega

/-- Exact nine-word accumulation for every equally sized block of at most 32 pairs. -/
@[step]
theorem block_kernel_spec {M S T : Type} (sum : Sum M)
    (lhs : Aeneas.Std.Slice (Element M S)) (rhs : Aeneas.Std.Slice (Element M T))
    (hlen : lhs.length = rhs.length) (hcount : lhs.length ≤ 32)
    (hbound : sumInteger sum + rawSum (fun a => val4 a.limbs)
      (fun b => val4 b.limbs) lhs.val rhs.val < B ^ 9) :
    CommonProductsAarch64.field.pasta.products.ProductSum.add_product_block sum lhs rhs ⦃ out =>
      sumInteger out = sumInteger sum + rawSum (fun a => val4 a.limbs)
        (fun b => val4 b.limbs) lhs.val rhs.val ⦄ := by
  let dot := fun i j => wordDot (fun a : Element M S => a.limbs) (fun b : Element M T => b.limbs)
    i j lhs.val rhs.val
  have hd00 : dot 0 0 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 0 0 lhs.val rhs.val hlen hcount
  have hd01 : dot 0 1 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 0 1 lhs.val rhs.val hlen hcount
  have hd10 : dot 1 0 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 1 0 lhs.val rhs.val hlen hcount
  have hd02 : dot 0 2 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 0 2 lhs.val rhs.val hlen hcount
  have hd11 : dot 1 1 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 1 1 lhs.val rhs.val hlen hcount
  have hd20 : dot 2 0 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 2 0 lhs.val rhs.val hlen hcount
  have hd03 : dot 0 3 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 0 3 lhs.val rhs.val hlen hcount
  have hd12 : dot 1 2 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 1 2 lhs.val rhs.val hlen hcount
  have hd21 : dot 2 1 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 2 1 lhs.val rhs.val hlen hcount
  have hd30 : dot 3 0 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 3 0 lhs.val rhs.val hlen hcount
  have hd13 : dot 1 3 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 1 3 lhs.val rhs.val hlen hcount
  have hd22 : dot 2 2 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 2 2 lhs.val rhs.val hlen hcount
  have hd31 : dot 3 1 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 3 1 lhs.val rhs.val hlen hcount
  have hd23 : dot 2 3 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 2 3 lhs.val rhs.val hlen hcount
  have hd32 : dot 3 2 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 3 2 lhs.val rhs.val hlen hcount
  have hd33 : dot 3 3 ≤ 32 * B ^ 2 :=
    word_dot_bound (fun a => a.limbs) (fun b => b.limbs) 3 3 lhs.val rhs.val hlen hcount
  have hlenNative : Aeneas.Std.Slice.len lhs = Aeneas.Std.Slice.len rhs := by scalar_tac
  rw [block_core_eq]
  unfold blockCore
  simp only [Bind.bind,hlenNative,massert,↓reduceIte,bind_ok]
  have hs0 := initial_columns_bound sum.wide[0]!
  have hv0 := initial_columns_value sum.wide[0]!
  have hrow0 : batchColumnsInteger (initialColumns sum.wide[0]!) + (dot 0 0) < B ^ 3 := by
    have h := comba_column_bound (batchColumnsInteger (initialColumns sum.wide[0]!)) (dot 0 0) 0 0 0 hs0 hd00 (by norm_num [B]) (by norm_num [B]) (by norm_num [B])
    simpa only [Nat.add_zero] using h
  step -grind with (accumulate_column_spec 0#usize 0#usize (by decide) (by decide)
    (initialColumns sum.wide[0]!) lhs rhs hlen (by change batchColumnsInteger (initialColumns sum.wide[0]!) + dot 0 0 < B ^ 3; omega))
    as ⟨columns0_0,hv0_0⟩
  change batchColumnsInteger columns0_0 = batchColumnsInteger (initialColumns sum.wide[0]!) + dot 0 0 at hv0_0
  step -grind with (batch_merge_columns_spec columns0_0 (by omega)) as ⟨column0,hm0⟩
  have hc0 : batchColumnInteger column0 = sum.wide[0]!.val + dot 0 0 := by omega
  step -grind with (batch_start_columns_spec sum.wide[1]! column0[1]! column0[2]!)
    as ⟨seed1,hv1,hs1⟩
  have hrow1 : batchColumnsInteger seed1 + (dot 0 1) + (dot 1 0) < B ^ 3 := by
    have h := comba_column_bound (batchColumnsInteger seed1) (dot 0 1) (dot 1 0) 0 0 hs1 hd01 hd10 (by norm_num [B]) (by norm_num [B])
    simpa only [Nat.add_zero] using h
  step -grind with (accumulate_column_spec 0#usize 1#usize (by decide) (by decide)
    seed1 lhs rhs hlen (by change batchColumnsInteger seed1 + dot 0 1 < B ^ 3; omega))
    as ⟨columns1_0,hv1_0⟩
  change batchColumnsInteger columns1_0 = batchColumnsInteger seed1 + dot 0 1 at hv1_0
  step -grind with (accumulate_column_spec 1#usize 0#usize (by decide) (by decide)
    columns1_0 lhs rhs hlen (by change batchColumnsInteger columns1_0 + dot 1 0 < B ^ 3; omega))
    as ⟨columns1_1,hv1_1⟩
  change batchColumnsInteger columns1_1 = batchColumnsInteger columns1_0 + dot 1 0 at hv1_1
  step -grind with (batch_merge_columns_spec columns1_1 (by omega)) as ⟨column1,hm1⟩
  have hc1 : batchColumnInteger column1 = sum.wide[1]!.val + column0[1]!.val + B * column0[2]!.val + (dot 0 1) + (dot 1 0) := by omega
  step -grind with (batch_start_columns_spec sum.wide[2]! column1[1]! column1[2]!)
    as ⟨seed2,hv2,hs2⟩
  have hrow2 : batchColumnsInteger seed2 + (dot 0 2) + (dot 1 1) + (dot 2 0) < B ^ 3 := by
    have h := comba_column_bound (batchColumnsInteger seed2) (dot 0 2) (dot 1 1) (dot 2 0) 0 hs2 hd02 hd11 hd20 (by norm_num [B])
    simpa only [Nat.add_zero] using h
  step -grind with (accumulate_column_spec 0#usize 2#usize (by decide) (by decide)
    seed2 lhs rhs hlen (by change batchColumnsInteger seed2 + dot 0 2 < B ^ 3; omega))
    as ⟨columns2_0,hv2_0⟩
  change batchColumnsInteger columns2_0 = batchColumnsInteger seed2 + dot 0 2 at hv2_0
  step -grind with (accumulate_column_spec 1#usize 1#usize (by decide) (by decide)
    columns2_0 lhs rhs hlen (by change batchColumnsInteger columns2_0 + dot 1 1 < B ^ 3; omega))
    as ⟨columns2_1,hv2_1⟩
  change batchColumnsInteger columns2_1 = batchColumnsInteger columns2_0 + dot 1 1 at hv2_1
  step -grind with (accumulate_column_spec 2#usize 0#usize (by decide) (by decide)
    columns2_1 lhs rhs hlen (by change batchColumnsInteger columns2_1 + dot 2 0 < B ^ 3; omega))
    as ⟨columns2_2,hv2_2⟩
  change batchColumnsInteger columns2_2 = batchColumnsInteger columns2_1 + dot 2 0 at hv2_2
  step -grind with (batch_merge_columns_spec columns2_2 (by omega)) as ⟨column2,hm2⟩
  have hc2 : batchColumnInteger column2 = sum.wide[2]!.val + column1[1]!.val + B * column1[2]!.val + (dot 0 2) + (dot 1 1) + (dot 2 0) := by omega
  step -grind with (batch_start_columns_spec sum.wide[3]! column2[1]! column2[2]!)
    as ⟨seed3,hv3,hs3⟩
  have hrow3 : batchColumnsInteger seed3 + (dot 0 3) + (dot 1 2) + (dot 2 1) + (dot 3 0) < B ^ 3 := by
    have h := comba_column_bound (batchColumnsInteger seed3) (dot 0 3) (dot 1 2) (dot 2 1) (dot 3 0) hs3 hd03 hd12 hd21 hd30
    simpa only [Nat.add_zero] using h
  step -grind with (accumulate_column_spec 0#usize 3#usize (by decide) (by decide)
    seed3 lhs rhs hlen (by change batchColumnsInteger seed3 + dot 0 3 < B ^ 3; omega))
    as ⟨columns3_0,hv3_0⟩
  change batchColumnsInteger columns3_0 = batchColumnsInteger seed3 + dot 0 3 at hv3_0
  step -grind with (accumulate_column_spec 1#usize 2#usize (by decide) (by decide)
    columns3_0 lhs rhs hlen (by change batchColumnsInteger columns3_0 + dot 1 2 < B ^ 3; omega))
    as ⟨columns3_1,hv3_1⟩
  change batchColumnsInteger columns3_1 = batchColumnsInteger columns3_0 + dot 1 2 at hv3_1
  step -grind with (accumulate_column_spec 2#usize 1#usize (by decide) (by decide)
    columns3_1 lhs rhs hlen (by change batchColumnsInteger columns3_1 + dot 2 1 < B ^ 3; omega))
    as ⟨columns3_2,hv3_2⟩
  change batchColumnsInteger columns3_2 = batchColumnsInteger columns3_1 + dot 2 1 at hv3_2
  step -grind with (accumulate_column_spec 3#usize 0#usize (by decide) (by decide)
    columns3_2 lhs rhs hlen (by change batchColumnsInteger columns3_2 + dot 3 0 < B ^ 3; omega))
    as ⟨columns3_3,hv3_3⟩
  change batchColumnsInteger columns3_3 = batchColumnsInteger columns3_2 + dot 3 0 at hv3_3
  step -grind with (batch_merge_columns_spec columns3_3 (by omega)) as ⟨column3,hm3⟩
  have hc3 : batchColumnInteger column3 = sum.wide[3]!.val + column2[1]!.val + B * column2[2]!.val + (dot 0 3) + (dot 1 2) + (dot 2 1) + (dot 3 0) := by omega
  step -grind with (batch_start_columns_spec sum.wide[4]! column3[1]! column3[2]!)
    as ⟨seed4,hv4,hs4⟩
  have hrow4 : batchColumnsInteger seed4 + (dot 1 3) + (dot 2 2) + (dot 3 1) < B ^ 3 := by
    have h := comba_column_bound (batchColumnsInteger seed4) (dot 1 3) (dot 2 2) (dot 3 1) 0 hs4 hd13 hd22 hd31 (by norm_num [B])
    simpa only [Nat.add_zero] using h
  step -grind with (accumulate_column_spec 1#usize 3#usize (by decide) (by decide)
    seed4 lhs rhs hlen (by change batchColumnsInteger seed4 + dot 1 3 < B ^ 3; omega))
    as ⟨columns4_0,hv4_0⟩
  change batchColumnsInteger columns4_0 = batchColumnsInteger seed4 + dot 1 3 at hv4_0
  step -grind with (accumulate_column_spec 2#usize 2#usize (by decide) (by decide)
    columns4_0 lhs rhs hlen (by change batchColumnsInteger columns4_0 + dot 2 2 < B ^ 3; omega))
    as ⟨columns4_1,hv4_1⟩
  change batchColumnsInteger columns4_1 = batchColumnsInteger columns4_0 + dot 2 2 at hv4_1
  step -grind with (accumulate_column_spec 3#usize 1#usize (by decide) (by decide)
    columns4_1 lhs rhs hlen (by change batchColumnsInteger columns4_1 + dot 3 1 < B ^ 3; omega))
    as ⟨columns4_2,hv4_2⟩
  change batchColumnsInteger columns4_2 = batchColumnsInteger columns4_1 + dot 3 1 at hv4_2
  step -grind with (batch_merge_columns_spec columns4_2 (by omega)) as ⟨column4,hm4⟩
  have hc4 : batchColumnInteger column4 = sum.wide[4]!.val + column3[1]!.val + B * column3[2]!.val + (dot 1 3) + (dot 2 2) + (dot 3 1) := by omega
  step -grind with (batch_start_columns_spec sum.wide[5]! column4[1]! column4[2]!)
    as ⟨seed5,hv5,hs5⟩
  have hrow5 : batchColumnsInteger seed5 + (dot 2 3) + (dot 3 2) < B ^ 3 := by
    have h := comba_column_bound (batchColumnsInteger seed5) (dot 2 3) (dot 3 2) 0 0 hs5 hd23 hd32 (by norm_num [B]) (by norm_num [B])
    simpa only [Nat.add_zero] using h
  step -grind with (accumulate_column_spec 2#usize 3#usize (by decide) (by decide)
    seed5 lhs rhs hlen (by change batchColumnsInteger seed5 + dot 2 3 < B ^ 3; omega))
    as ⟨columns5_0,hv5_0⟩
  change batchColumnsInteger columns5_0 = batchColumnsInteger seed5 + dot 2 3 at hv5_0
  step -grind with (accumulate_column_spec 3#usize 2#usize (by decide) (by decide)
    columns5_0 lhs rhs hlen (by change batchColumnsInteger columns5_0 + dot 3 2 < B ^ 3; omega))
    as ⟨columns5_1,hv5_1⟩
  change batchColumnsInteger columns5_1 = batchColumnsInteger columns5_0 + dot 3 2 at hv5_1
  step -grind with (batch_merge_columns_spec columns5_1 (by omega)) as ⟨column5,hm5⟩
  have hc5 : batchColumnInteger column5 = sum.wide[5]!.val + column4[1]!.val + B * column4[2]!.val + (dot 2 3) + (dot 3 2) := by omega
  step -grind with (batch_start_columns_spec sum.wide[6]! column5[1]! column5[2]!)
    as ⟨seed6,hv6,hs6⟩
  have hrow6 : batchColumnsInteger seed6 + (dot 3 3) < B ^ 3 := by
    have h := comba_column_bound (batchColumnsInteger seed6) (dot 3 3) 0 0 0 hs6 hd33 (by norm_num [B]) (by norm_num [B]) (by norm_num [B])
    simpa only [Nat.add_zero] using h
  step -grind with (accumulate_column_spec 3#usize 3#usize (by decide) (by decide)
    seed6 lhs rhs hlen (by change batchColumnsInteger seed6 + dot 3 3 < B ^ 3; omega))
    as ⟨columns6_0,hv6_0⟩
  change batchColumnsInteger columns6_0 = batchColumnsInteger seed6 + dot 3 3 at hv6_0
  step -grind with (batch_merge_columns_spec columns6_0 (by omega)) as ⟨column6,hm6⟩
  have hc6 : batchColumnInteger column6 = sum.wide[6]!.val + column5[1]!.val + B * column5[2]!.val + (dot 3 3) := by omega
  step -grind with (batch_start_column_spec sum.wide[7]! column6[1]! column6[2]!)
    as ⟨column7,hc7,hc7bound⟩
  let outWide := sum.wide.set 0#usize column0[0]! |>.set 1#usize column1[0]! |>.set 2#usize column2[0]!
    |>.set 3#usize column3[0]! |>.set 4#usize column4[0]! |>.set 5#usize column5[0]!
    |>.set 6#usize column6[0]! |>.set 7#usize column7[0]!
  have hconv := word_dot_convolution (fun a : Element M S => a.limbs)
    (fun b : Element M T => b.limbs) lhs.val rhs.val
  change rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val =
    dot 0 0 + B * (dot 0 1 + dot 1 0) + B ^ 2 * (dot 0 2 + dot 1 1 + dot 2 0) +
    B ^ 3 * (dot 0 3 + dot 1 2 + dot 2 1 + dot 3 0) +
    B ^ 4 * (dot 1 3 + dot 2 2 + dot 3 1) + B ^ 5 * (dot 2 3 + dot 3 2) + B ^ 6 * dot 3 3 at hconv
  have hvalue : val8 outWide + B ^ 8 *
      (sum.carry.val + column7[1]!.val + B * column7[2]!.val) =
      sumInteger sum + rawSum (fun a => val4 a.limbs) (fun b => val4 b.limbs) lhs.val rhs.val := by
    simp only [sumInteger,sumToNative,Native.sumInteger,Native.accumulatorValue]
    simp [outWide,val8]
    dsimp only [batchColumnInteger] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    norm_num [B,R] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hconv ⊢
    omega
  have hhigh : column7[2]!.val = 0 := by
    norm_num [B] at hvalue hbound ⊢
    omega
  have hhighWord : column7[2]! = 0#u64 := by scalar_tac
  have hcarryBound : sum.carry.val + column7[1]!.val < B := by
    norm_num [B] at hvalue hbound ⊢
    omega
  simp only [hhighWord,massert,↓reduceIte,bind_ok,lift,Std.uncurry]
  obtain ⟨carry,overflow,hresult,hcarry⟩ := batch_overflowing_add_result sum.carry column7[1]!
  rw [hresult]
  simp only [bind_ok]
  have hno : overflow = false := by
    cases overflow <;> simp_all only [Bool.toNat_true,Bool.toNat_false,Nat.mul_one,Nat.mul_zero,Nat.add_zero]
    norm_num [B] at hcarry hcarryBound
    omega
  subst overflow
  simp only [Bool.false_eq_true,not_false_eq_true,massert,↓reduceIte,bind_ok,WP.spec_ok]
  change sumInteger {sum with wide := outWide, carry} = _
  simp only [sumInteger,sumToNative,Native.sumInteger,Native.accumulatorValue]
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hcarry
  simp only [hhigh,Nat.mul_zero,Nat.add_zero] at hvalue
  simp only [sumInteger,sumToNative,Native.sumInteger,Native.accumulatorValue] at hvalue
  norm_num [B,R] at hcarry hvalue ⊢
  omega

#print axioms initial_columns_value
#print axioms initial_columns_bound
#print axioms block_kernel_spec
end UdonVerify.ProductBlock
