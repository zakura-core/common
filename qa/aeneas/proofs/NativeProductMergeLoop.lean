import NativeProductMergeExpansion
open Aeneas Std Result
namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
open NativeField.zakura_udon.field.pasta.word

def mergeRaw (a b : A8) : Result (A8 × U64) := do
  let (r0,c0) ← adc a[0]! b[0]! 0#u64
  let (r1,c1) ← adc a[1]! b[1]! c0
  let (r2,c2) ← adc a[2]! b[2]! c1
  let (r3,c3) ← adc a[3]! b[3]! c2
  let (r4,c4) ← adc a[4]! b[4]! c3
  let (r5,c5) ← adc a[5]! b[5]! c4
  let (r6,c6) ← adc a[6]! b[6]! c5
  let (r7,c7) ← adc a[7]! b[7]! c6
  ok (Array.make 8#usize [r0,r1,r2,r3,r4,r5,r6,r7],c7)

theorem merge_expansion_raw_eq {M : Type} (inst : Modulus M) (sum other : Sum M) :
    mergeExpansion inst sum other = (do
      let (wide,carry) ← mergeRaw sum.wide other.wide
      let (sumCarry,overflow) ← adc sum.carry other.carry carry
      NativeField.zakura_udon.field.pasta.products.ProductSum.fold_overflow inst
        {sum with wide,carry:=sumCarry} overflow) := by
  unfold mergeExpansion mergeRaw
  simp only [Std.bind_assoc,bind_ok,Std.uncurry,bind_tc_eq]
  with_unfolding_all rfl

@[step]
theorem merge_raw_spec (a b : A8) : mergeRaw a b
    ⦃ out=>out.snd.val≤1 ∧ val8 out.fst+R^2*out.snd.val=val8 a+val8 b ⦄ := by
  unfold mergeRaw
  try simp only [Std.uncurry,bind_tc_eq,Std.bind_assoc]
  obtain ⟨r0,c0,hr0,h0⟩ := product_adc_result a[0]! b[0]! 0#u64
  rw [hr0]
  simp only [bind_ok,Std.uncurry]
  obtain ⟨r1,c1,hr1,h1⟩ := product_adc_result a[1]! b[1]! c0
  rw [hr1]
  simp only [bind_ok,Std.uncurry]
  obtain ⟨r2,c2,hr2,h2⟩ := product_adc_result a[2]! b[2]! c1
  rw [hr2]
  simp only [bind_ok,Std.uncurry]
  obtain ⟨r3,c3,hr3,h3⟩ := product_adc_result a[3]! b[3]! c2
  rw [hr3]
  simp only [bind_ok,Std.uncurry]
  obtain ⟨r4,c4,hr4,h4⟩ := product_adc_result a[4]! b[4]! c3
  rw [hr4]
  simp only [bind_ok,Std.uncurry]
  obtain ⟨r5,c5,hr5,h5⟩ := product_adc_result a[5]! b[5]! c4
  rw [hr5]
  simp only [bind_ok,Std.uncurry]
  obtain ⟨r6,c6,hr6,h6⟩ := product_adc_result a[6]! b[6]! c5
  rw [hr6]
  simp only [bind_ok,Std.uncurry]
  obtain ⟨r7,c7,hr7,h7⟩ := product_adc_result a[7]! b[7]! c6
  rw [hr7]
  simp only [bind_ok,Std.uncurry]
  try simp only [WP.spec_ok]
  simp only [Array.getElem!_Nat_eq] at h0 h1 h2 h3 h4 h5 h6 h7
  change r0.val+B*c0.val=a.val[0]!.val+b.val[0]!.val+0 at h0
  have hvalue : val8 (Array.make 8#usize [r0,r1,r2,r3,r4,r5,r6,r7])+R^2*c7.val=val8 a+val8 b := by
    simp only [val8,Array.getElem!_Nat_eq,Array.make_val]
    simp only [List.getElem!_cons_zero,List.getElem!_cons_succ]
    unfold R
    linear_combination h0+B*h1+B^2*h2+B^3*h3+B^4*h4+B^5*h5+B^6*h6+B^7*h7
  refine ⟨?_,hvalue⟩
  have ha:=val8_lt a
  have hb:=val8_lt b
  norm_num [R,B] at hvalue ha hb
  omega

#print axioms merge_expansion_raw_eq
#print axioms merge_raw_spec
end UdonVerify.Native
