import Proofs

open Aeneas Std Result

namespace UdonVerify

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

abbrev B : Nat := 2^64
abbrev R : Nat := B^4
abbrev A4 := Aeneas.Std.Array U64 4#usize
abbrev A8 := Aeneas.Std.Array U64 8#usize

def val4 (a : A4) : Nat :=
  a[0]!.val + B*a[1]!.val + B^2*a[2]!.val + B^3*a[3]!.val

def val8 (a : A8) : Nat :=
  a[0]!.val + B*a[1]!.val + B^2*a[2]!.val + B^3*a[3]!.val +
  B^4*a[4]!.val + B^5*a[5]!.val + B^6*a[6]!.val + B^7*a[7]!.val

theorem val4_lt (a : A4) : val4 a < R := by
  unfold val4 R B
  scalar_tac

theorem val8_lt (a : A8) : val8 a < R^2 := by
  unfold val8 R B
  scalar_tac

@[step]
theorem adc_identity (lhs rhs carry : U64) :
    zakura_udon.field.pasta.word.adc lhs rhs carry ⦃ lo hi =>
      lo.val + B * hi.val = lhs.val + rhs.val + carry.val ⦄ := by
  step with adc_spec as ⟨lo, hi, hlo, hhi⟩
  have hd := Nat.mod_add_div (lhs.val + rhs.val + carry.val) B
  simp only [B] at hd ⊢
  omega

@[step]
theorem mac_identity (accumulator lhs rhs carry : U64) :
    zakura_udon.field.pasta.word.mac accumulator lhs rhs carry ⦃ lo hi =>
      lo.val + B * hi.val = lhs.val * rhs.val + accumulator.val + carry.val ⦄ := by
  step with mac_spec as ⟨lo, hi, hlo, hhi⟩
  have hd := Nat.mod_add_div (lhs.val * rhs.val + accumulator.val + carry.val) B
  simp only [B] at hd ⊢
  omega

@[step]
theorem kernel_adc_identity (lhs rhs carry : U64) :
    zakura_udon.field.pasta.word.adc lhs rhs carry ⦃ lo hi =>
      lo.val + B * hi.val = lhs.val + rhs.val + carry.val ⦄ := by
  simpa only [zakura_udon.field.pasta.word.adc,
    zakura_udon.field.pasta.word.adc] using adc_identity lhs rhs carry

@[step]
theorem kernel_mac_identity (accumulator lhs rhs carry : U64) :
    zakura_udon.field.pasta.word.mac accumulator lhs rhs carry ⦃ lo hi =>
      lo.val + B * hi.val = lhs.val * rhs.val + accumulator.val + carry.val ⦄ := by
  simpa only [zakura_udon.field.pasta.word.mac,
    zakura_udon.field.pasta.word.mac] using mac_identity accumulator lhs rhs carry

@[step]
theorem kernel_sbb_identity (lhs rhs borrow : U64) (hb : borrow.val ≤ 1) :
    zakura_udon.field.pasta.word.sbb lhs rhs borrow ⦃ result =>
      result.2.val ≤ 1 ∧ result.1.val + rhs.val + borrow.val = lhs.val + B * result.2.val ⦄ := by
  simpa only [zakura_udon.field.pasta.word.sbb,
    zakura_udon.field.pasta.word.sbb] using sbb_spec lhs rhs borrow hb

end UdonVerify
