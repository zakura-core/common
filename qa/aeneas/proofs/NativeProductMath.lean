import NativeWideParameters

namespace UdonVerify.Native
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

/-- The integer stored by the nine-word deferred-product accumulator. -/
def accumulatorValue (wide : A8) (carry : Aeneas.Std.U64) : Nat :=
  val8 wide + R ^ 2 * carry.val

theorem partial_reduce_congruence (p low upper carry high448 radix2 : Nat)
    (h448 : Nat.ModEq p high448 (B ^ 7))
    (h512 : Nat.ModEq p radix2 (R ^ 2)) :
    Nat.ModEq p (low + upper * high448 + carry * radix2)
      (low + B ^ 7 * upper + R ^ 2 * carry) := by
  convert (h448.mul_left upper).add (h512.mul_left carry) |>.add_left low using 1 <;> ring

theorem partial_reduce_bound {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (low upper carry high448 radix2 : Nat)
    (hlow : low < B ^ 7) (hupper : upper < B) (hcarry : carry < B)
    (h448 : high448 < val4 params.modulus)
    (h512 : radix2 < val4 params.modulus) :
    low + upper * high448 + carry * radix2 < 2 * B ^ 7 ∧
    low + upper * high448 + carry * radix2 < val4 params.modulus * R := by
  have hB : 0 < B := by norm_num [B]
  have hprod448 : upper * high448 < B * val4 params.modulus :=
    _root_.lt_of_le_of_lt (Nat.mul_le_mul_right high448 (Nat.le_of_lt hupper))
      (Nat.mul_lt_mul_of_pos_left h448 hB)
  have hprod512 : carry * radix2 < B * val4 params.modulus :=
    _root_.lt_of_le_of_lt (Nat.mul_le_mul_right radix2 (Nat.le_of_lt hcarry))
      (Nat.mul_lt_mul_of_pos_left h512 hB)
  have hsum : low + upper * high448 + carry * radix2 <
      B ^ 7 + 2 * B * val4 params.modulus := by
    nlinarith only [hlow, hprod448, hprod512]
  have hpUpper := params.thrice_lt
  have hpLower := params.offset_positive
  norm_num [R, B] at hpUpper hpLower hsum ⊢
  constructor <;> omega

theorem two_raw_products_bound {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (constants : WideFieldParameters inst params) (low high : Nat)
    (hlow : low < R) (hhigh : high < R) :
    low * val4 constants.conversion.radix2 + high * val4 constants.radix3 <
      val4 params.modulus * R := by
  have hleLow := Nat.mul_le_mul_right (val4 constants.conversion.radix2) (Nat.le_of_lt hlow)
  have hleHigh := Nat.mul_le_mul_right (val4 constants.radix3) (Nat.le_of_lt hhigh)
  have hstrict := Nat.mul_lt_mul_of_pos_left constants.wide_bound (show 0 < R by norm_num [R, B])
  nlinarith only [hleLow, hleHigh, hstrict]

theorem horner_raw_products_bound {M : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst))
    (constants : WideFieldParameters inst params) (value digit : Nat)
    (hvalue : value < 2 * val4 params.modulus) (hdigit : digit < R) :
    value * val4 constants.conversion.radix2 + digit * val4 constants.conversion.radix2 <
      val4 params.modulus * R := by
  have hle := Nat.mul_le_mul_right (val4 constants.conversion.radix2)
    (show value + digit ≤ 2 * val4 params.modulus + R by omega)
  nlinarith only [hle, constants.horner_bound]

#print axioms partial_reduce_congruence
#print axioms partial_reduce_bound
#print axioms two_raw_products_bound
#print axioms horner_raw_products_bound

end UdonVerify.Native
