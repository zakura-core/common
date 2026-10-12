import NativeProductLimits
import NativeProductHigh

open Aeneas Std Result
namespace UdonVerify.Products
open UdonVerify.Native
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

/-- The unreduced integer accumulated by a pairwise product iterator. -/
def rawSum {α β : Type} (left : α → Nat) (right : β → Nat) : List α → List β → Nat
  | a :: xs, b :: ys => left a * right b + rawSum left right xs ys
  | _, _ => 0

def stateWeight (reduced : Bool) : Nat := if reduced then 1 else 2

theorem raw_sum_bound {α β : Type} (left : α → Nat) (right : β → Nat)
    (aBound bBound : Nat) (lhs : List α) (rhs : List β)
    (hlen : lhs.length = rhs.length)
    (ha : ∀ a ∈ lhs, left a < aBound) (hb : ∀ b ∈ rhs, right b < bBound) :
    rawSum left right lhs rhs + lhs.length ≤ lhs.length * (aBound * bBound) := by
  induction lhs generalizing rhs with
  | nil => simp [rawSum]
  | cons a xs ih =>
    cases rhs with
    | nil => simp at hlen
    | cons b ys =>
      have ha0 := ha a (by simp)
      have hb0 := hb b (by simp)
      have hpositive : 0 < bBound := by omega
      have hfirst := Nat.mul_le_mul_left (left a) (Nat.le_of_lt hb0)
      have hsecond := Nat.mul_lt_mul_of_pos_right ha0 hpositive
      have hproduct : left a * right b + 1 ≤ aBound * bBound := by omega
      have htail := ih ys (by simpa using hlen)
        (fun x hx => ha x (by simp [hx])) (fun y hy => hb y (by simp [hy]))
      simp only [rawSum, List.length_cons, Nat.succ_mul]
      omega

theorem raw_sum_append {α β : Type} (left : α → Nat) (right : β → Nat)
    (xs us : List α) (ys vs : List β) (hlen : xs.length = ys.length) :
    rawSum left right (xs ++ us) (ys ++ vs) =
      rawSum left right xs ys + rawSum left right us vs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [rawSum]
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.cons_append, rawSum]
      rw [ih ys (by simpa using hlen), Nat.add_assoc]

/-- State-sensitive bound before the optional high-half fold. -/
theorem short_sum_scaled_bound {α β : Type} (left : α → Nat) (right : β → Nat)
    (p : Nat) (hp : 0 < p) (hthrice : 3 * p < R)
    (s t : Bool) (lhs : List α) (rhs : List β)
    (hlen : lhs.length = rhs.length) (hshort : lhs.length ≤ 3)
    (ha : ∀ a ∈ lhs, left a < stateWeight s * p)
    (hb : ∀ b ∈ rhs, right b < stateWeight t * p) :
    rawSum left right lhs rhs < (stateWeight s * stateWeight t) * p * R := by
  have hsum := raw_sum_bound left right (stateWeight s * p) (stateWeight t * p)
    lhs rhs hlen ha hb
  have hupper := Nat.mul_le_mul_right ((stateWeight s * p) * (stateWeight t * p)) hshort
  have hfactor : 0 < (stateWeight s * stateWeight t) * p := by
    cases s <;> cases t <;> simp [stateWeight] <;> omega
  have hscaled := Nat.mul_lt_mul_of_pos_left hthrice hfactor
  nlinarith only [hsum, hupper, hscaled]

theorem short_sum_wide_bound {M α β : Type} (inst : Modulus M)
    (params : PastaParameters (kernelInst inst)) (left : α → Nat) (right : β → Nat)
    (lhs : List α) (rhs : List β) (hlen : lhs.length = rhs.length) (hshort : lhs.length ≤ 3)
    (ha : ∀ a ∈ lhs, left a < 2 * val4 params.modulus)
    (hb : ∀ b ∈ rhs, right b < 2 * val4 params.modulus) :
    rawSum left right lhs rhs < R ^ 2 := by
  have hsum := raw_sum_bound left right (2 * val4 params.modulus) (2 * val4 params.modulus)
    lhs rhs hlen ha hb
  have hupper := Nat.mul_le_mul_right ((2 * val4 params.modulus) * (2 * val4 params.modulus)) hshort
  nlinarith only [hsum, hupper, product_three_loose_limit inst params]

/-- Every physically bounded 64-bit slice fits the nine-word accumulator. -/
theorem bounded_sum_fits_accumulator {α β : Type} (left : α → Nat) (right : β → Nat)
    (lhs : List α) (rhs : List β) (hlen : lhs.length = rhs.length) (hcount : lhs.length < B)
    (ha : ∀ a ∈ lhs, left a < R) (hb : ∀ b ∈ rhs, right b < R) :
    rawSum left right lhs rhs < B ^ 9 := by
  have hsum := raw_sum_bound left right R R lhs rhs hlen ha hb
  have hpositive : 0 < R * R := by norm_num [R, B]
  calc
    rawSum left right lhs rhs ≤ lhs.length * (R * R) := by omega
    _ < B * (R * R) := Nat.mul_lt_mul_of_pos_right hcount hpositive
    _ = B ^ 9 := by unfold R; ring

theorem raw_sum_decoded {α β : Type} (left : α → Nat) (right : β → Nat)
    (p inverse : Nat) (lhs : List α) (rhs : List β) :
    Nat.ModEq p (rawSum (fun a => left a * inverse % p)
      (fun b => right b * inverse % p) lhs rhs)
      (rawSum left right lhs rhs * inverse ^ 2) := by
  induction lhs generalizing rhs with
  | nil => simp [rawSum, Nat.ModEq]
  | cons a xs ih =>
    cases rhs with
    | nil => simp [rawSum, Nat.ModEq]
    | cons b ys =>
      have hproduct : Nat.ModEq p
          ((left a * inverse % p) * (right b * inverse % p))
          ((left a * right b) * inverse ^ 2) := by
        have ha : Nat.ModEq p (left a * inverse % p) (left a * inverse) := by
          simp only [Nat.ModEq, Nat.mod_mod]
        have hb : Nat.ModEq p (right b * inverse % p) (right b * inverse) := by
          simp only [Nat.ModEq, Nat.mod_mod]
        convert ha.mul hb using 1 <;> ring
      simpa only [rawSum, Nat.add_mul] using hproduct.add (ih ys)

theorem short_sum_high_bound (wide : A8) (p : Nat) (s t : Bool)
    (hbound : val8 wide < (stateWeight s * stateWeight t) * p * R)
    (hloose : (!s || !t) = true) :
    val4 (productHigh wide) < (if !s && !t then 4 else 2) * p := by
  have hvalue := product_halves_value wide
  have hR : 0 < R := by norm_num [R, B]
  cases s <;> cases t <;> simp [stateWeight] at hbound hloose ⊢ <;>
    nlinarith only [hbound, hvalue, hR]

/-- The removed AArch64 branch is contradictory for every slice length. -/
theorem aarch64_four_lane_unreachable (length : Nat)
    (hblock : ¬ 32 ≤ length) (hportable : ¬ length < 64) : False := by omega

#print axioms raw_sum_bound
#print axioms raw_sum_append
#print axioms short_sum_scaled_bound
#print axioms short_sum_wide_bound
#print axioms bounded_sum_fits_accumulator
#print axioms raw_sum_decoded
#print axioms short_sum_high_bound
#print axioms aarch64_four_lane_unreachable
end UdonVerify.Products
