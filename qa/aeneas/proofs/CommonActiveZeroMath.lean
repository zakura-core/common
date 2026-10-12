import CommonFG62FirstUpdate
import CommonInvHelpers.Funs

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def active62Normalized (a : Signed62) (len : Nat) : Prop :=
  ∀ k : Fin 5, k.val + 1 < len → 0 ≤ a[k.val]!.val ∧ a[k.val]!.val < signedRadix

theorem radix_zero_split (digit tail : Int)
    (hd : 0 ≤ digit ∧ digit < signedRadix) (hv : digit + signedRadix * tail = 0) :
    digit = 0 ∧ tail = 0 := by
  norm_num only [signedRadix] at hd hv
  omega

theorem active62_zero_iff (a : Signed62) (len : Nat) (hlen : 1 ≤ len ∧ len ≤ 5)
    (hn : active62Normalized a len) :
    active62Value a len = 0 ↔ ∀ k : Fin 5, k.val < len → a[k.val]!.val = 0 := by
  constructor
  · intro hvalue
    have hcases : len = 1 ∨ len = 2 ∨ len = 3 ∨ len = 4 ∨ len = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · have hpoly : a[0]!.val = 0 := by
        norm_num only [active62Value, Finset.sum_range_succ, Finset.sum_range_zero,
          pow_zero, one_mul, zero_add] at hvalue
        convert hvalue using 1 <;> ring
      have hz0 : a[0]!.val = 0 := hpoly
      intro k hk
      fin_cases k <;> simp_all
    · have hpoly : a[0]!.val + signedRadix * (a[1]!.val) = 0 := by
        norm_num only [active62Value, Finset.sum_range_succ, Finset.sum_range_zero,
          pow_zero, one_mul, zero_add] at hvalue
        convert hvalue using 1 <;> ring
      obtain ⟨hz0, hrest0⟩ := radix_zero_split a[0]!.val
        (a[1]!.val) (hn ⟨0, by decide⟩ (by decide)) hpoly
      have hz1 : a[1]!.val = 0 := hrest0
      intro k hk
      fin_cases k <;> simp_all
    · have hpoly : a[0]!.val + signedRadix * (a[1]!.val + signedRadix * (a[2]!.val)) = 0 := by
        norm_num only [active62Value, Finset.sum_range_succ, Finset.sum_range_zero,
          pow_zero, one_mul, zero_add] at hvalue
        convert hvalue using 1 <;> ring
      obtain ⟨hz0, hrest0⟩ := radix_zero_split a[0]!.val
        (a[1]!.val + signedRadix * (a[2]!.val)) (hn ⟨0, by decide⟩ (by decide)) hpoly
      obtain ⟨hz1, hrest1⟩ := radix_zero_split a[1]!.val
        (a[2]!.val) (hn ⟨1, by decide⟩ (by decide)) hrest0
      have hz2 : a[2]!.val = 0 := hrest1
      intro k hk
      fin_cases k <;> simp_all
    · have hpoly : a[0]!.val + signedRadix * (a[1]!.val + signedRadix * (a[2]!.val + signedRadix * (a[3]!.val))) = 0 := by
        norm_num only [active62Value, Finset.sum_range_succ, Finset.sum_range_zero,
          pow_zero, one_mul, zero_add] at hvalue
        convert hvalue using 1 <;> ring
      obtain ⟨hz0, hrest0⟩ := radix_zero_split a[0]!.val
        (a[1]!.val + signedRadix * (a[2]!.val + signedRadix * (a[3]!.val))) (hn ⟨0, by decide⟩ (by decide)) hpoly
      obtain ⟨hz1, hrest1⟩ := radix_zero_split a[1]!.val
        (a[2]!.val + signedRadix * (a[3]!.val)) (hn ⟨1, by decide⟩ (by decide)) hrest0
      obtain ⟨hz2, hrest2⟩ := radix_zero_split a[2]!.val
        (a[3]!.val) (hn ⟨2, by decide⟩ (by decide)) hrest1
      have hz3 : a[3]!.val = 0 := hrest2
      intro k hk
      fin_cases k <;> simp_all
    · have hpoly : a[0]!.val + signedRadix * (a[1]!.val + signedRadix * (a[2]!.val + signedRadix * (a[3]!.val + signedRadix * (a[4]!.val)))) = 0 := by
        norm_num only [active62Value, Finset.sum_range_succ, Finset.sum_range_zero,
          pow_zero, one_mul, zero_add] at hvalue
        convert hvalue using 1 <;> ring
      obtain ⟨hz0, hrest0⟩ := radix_zero_split a[0]!.val
        (a[1]!.val + signedRadix * (a[2]!.val + signedRadix * (a[3]!.val + signedRadix * (a[4]!.val)))) (hn ⟨0, by decide⟩ (by decide)) hpoly
      obtain ⟨hz1, hrest1⟩ := radix_zero_split a[1]!.val
        (a[2]!.val + signedRadix * (a[3]!.val + signedRadix * (a[4]!.val))) (hn ⟨1, by decide⟩ (by decide)) hrest0
      obtain ⟨hz2, hrest2⟩ := radix_zero_split a[2]!.val
        (a[3]!.val + signedRadix * (a[4]!.val)) (hn ⟨2, by decide⟩ (by decide)) hrest1
      obtain ⟨hz3, hrest3⟩ := radix_zero_split a[3]!.val
        (a[4]!.val) (hn ⟨3, by decide⟩ (by decide)) hrest2
      have hz4 : a[4]!.val = 0 := hrest3
      intro k hk
      fin_cases k <;> simp_all
  · intro hall
    unfold active62Value
    apply Finset.sum_eq_zero
    intro k hk
    have hklt := Finset.mem_range.mp hk
    rw [hall ⟨k, by omega⟩ hklt]
    ring

theorem signed_or_eq_zero (a b : I64) :
    a ||| b = 0#i64 ↔ a = 0#i64 ∧ b = 0#i64 := by
  constructor
  · intro h
    have hb := congrArg IScalar.bv h
    change a.bv ||| b.bv = 0#64 at hb
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp hb
    exact ⟨I64.bv_eq_imp_eq a 0#i64 ha, I64.bv_eq_imp_eq b 0#i64 hb⟩
  · rintro ⟨rfl, rfl⟩
    rfl

#print axioms radix_zero_split
#print axioms active62_zero_iff
#print axioms signed_or_eq_zero
end UdonVerify.CommonSigned62
