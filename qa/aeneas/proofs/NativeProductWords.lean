import NativeWideAdd
import NativeProductMath

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev Sum := NativeField.zakura_udon.field.pasta.products.ProductSum

def val7 (wide : A8) : Nat :=
  wide[0]!.val + B * wide[1]!.val + B ^ 2 * wide[2]!.val + B ^ 3 * wide[3]!.val +
    B ^ 4 * wide[4]!.val + B ^ 5 * wide[5]!.val + B ^ 6 * wide[6]!.val

def sumInteger {M : Type} (sum : Sum M) : Nat := accumulatorValue sum.wide sum.carry

def sumValue {M : Type} (p inverse : Nat) (sum : Sum M) : Nat :=
  (sumInteger sum*inverse^2)%p

theorem val8_split (wide : A8) : val8 wide = val7 wide + B ^ 7 * wide[7]!.val := by
  rfl

theorem val7_lt (wide : A8) : val7 wide < B ^ 7 := by
  unfold val7 B
  scalar_tac

@[step]
theorem native_adc_identity (lhs rhs carry : U64) :
    NativeField.zakura_udon.field.pasta.word.adc lhs rhs carry
      ⦃ out => out.fst.val+B*out.snd.val=lhs.val+rhs.val+carry.val ⦄ := by
  rw [native_wide_adc_eq]
  exact slice_adc_identity lhs rhs carry

theorem product_mac_result (accumulator lhs rhs carry : U64) :
    ∃ lo hi : U64,
      NativeField.zakura_udon.field.pasta.word.mac accumulator lhs rhs carry = ok (lo, hi) ∧
      lo.val + B * hi.val = lhs.val * rhs.val + accumulator.val + carry.val := by
  obtain ⟨pair, hresult, hvalue⟩ := WP.spec_imp_exists (kernel_mac_identity accumulator lhs rhs carry)
  rcases pair with ⟨lo, hi⟩
  exact ⟨lo, hi, by rw [mac_eq]; exact hresult, hvalue⟩

theorem product_adc_result (lhs rhs carry : U64) :
    ∃ lo hi : U64,
      NativeField.zakura_udon.field.pasta.word.adc lhs rhs carry = ok (lo, hi) ∧
      lo.val + B * hi.val = lhs.val + rhs.val + carry.val := by
  obtain ⟨pair, hresult, hvalue⟩ := WP.spec_imp_exists (native_adc_identity lhs rhs carry)
  rcases pair with ⟨lo, hi⟩
  exact ⟨lo, hi, hresult, hvalue⟩

theorem adc_carry_le_one (lhs rhs carry lo hi : U64) (hcarry : carry.val ≤ 1)
    (hvalue : lo.val + B * hi.val = lhs.val + rhs.val + carry.val) : hi.val ≤ 1 := by
  norm_num [B] at hvalue
  scalar_tac

theorem partial_coefficient_bound {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (upper carry : U64) (a b : A4)
    (ha : val4 a < val4 params.modulus) (hb : val4 b < val4 params.modulus) :
    upper.val * val4 a + carry.val * val4 b < B ^ 5 := by
  have hB : 0 < B := by norm_num [B]
  have hu : upper.val < B := by norm_num only [B]; scalar_tac
  have hc : carry.val < B := by norm_num only [B]; scalar_tac
  have hfirst : upper.val * val4 a < B * val4 params.modulus :=
    _root_.lt_of_le_of_lt (Nat.mul_le_mul_right (val4 a) (Nat.le_of_lt hu))
      (Nat.mul_lt_mul_of_pos_left ha hB)
  have hsecond : carry.val * val4 b < B * val4 params.modulus :=
    _root_.lt_of_le_of_lt (Nat.mul_le_mul_right (val4 b) (Nat.le_of_lt hc))
      (Nat.mul_lt_mul_of_pos_left hb hB)
  have hsum : upper.val * val4 a + carry.val * val4 b < 2 * B * val4 params.modulus := by
    nlinarith only [hfirst, hsecond]
  have hp := params.thrice_lt
  have hlimit : 2 * B * val4 params.modulus < B ^ 5 := by
    norm_num [B, R] at hp ⊢
    omega
  exact _root_.lt_trans hsum hlimit

#print axioms product_mac_result
#print axioms partial_coefficient_bound

end UdonVerify.Native
