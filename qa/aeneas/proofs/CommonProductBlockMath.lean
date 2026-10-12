import CommonProductSliceMath
import CommonCombaColumns

open Aeneas Std Result
namespace UdonVerify.ProductBlock
open UdonVerify.Products
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

/-- The contribution of a single pair of limb positions to a block. -/
def wordDot {α β : Type} (left : α → A4) (right : β → A4)
    (i j : Nat) (lhs : List α) (rhs : List β) : Nat :=
  rawSum (fun a => (left a)[i]!.val) (fun b => (right b)[j]!.val) lhs rhs

/-- At most 32 word products fit far below a three-word Comba column. -/
theorem word_dot_bound {α β : Type} (left : α → A4) (right : β → A4)
    (i j : Nat) (lhs : List α) (rhs : List β)
    (hlen : lhs.length = rhs.length) (hcount : lhs.length ≤ 32) :
    wordDot left right i j lhs rhs ≤ 32 * B ^ 2 := by
  have hsum := raw_sum_bound (fun a => (left a)[i]!.val)
    (fun b => (right b)[j]!.val) B B lhs rhs hlen
    (by intro a ha; have h := ((left a)[i]!).hmax; norm_num [UScalar.max, UScalarTy.U64_numBits_eq, B] at *; omega)
    (by intro b hb; have h := ((right b)[j]!).hmax; norm_num [UScalar.max, UScalarTy.U64_numBits_eq, B] at *; omega)
  have hscaled := Nat.mul_le_mul_right (B * B) hcount
  dsimp only [wordDot]
  nlinarith only [hsum,hscaled]

/-- The seven Comba columns are the convolution of the four input limbs. -/
theorem word_dot_convolution {α β : Type} (left : α → A4) (right : β → A4)
    (lhs : List α) (rhs : List β) :
    rawSum (fun a => val4 (left a)) (fun b => val4 (right b)) lhs rhs =
      wordDot left right 0 0 lhs rhs +
      B * (wordDot left right 0 1 lhs rhs + wordDot left right 1 0 lhs rhs) +
      B ^ 2 * (wordDot left right 0 2 lhs rhs + wordDot left right 1 1 lhs rhs +
        wordDot left right 2 0 lhs rhs) +
      B ^ 3 * (wordDot left right 0 3 lhs rhs + wordDot left right 1 2 lhs rhs +
        wordDot left right 2 1 lhs rhs + wordDot left right 3 0 lhs rhs) +
      B ^ 4 * (wordDot left right 1 3 lhs rhs + wordDot left right 2 2 lhs rhs +
        wordDot left right 3 1 lhs rhs) +
      B ^ 5 * (wordDot left right 2 3 lhs rhs + wordDot left right 3 2 lhs rhs) +
      B ^ 6 * wordDot left right 3 3 lhs rhs := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> simp [rawSum,wordDot]
  | cons a xs ih =>
    cases rhs with
    | nil => simp [rawSum,wordDot]
    | cons b ys =>
      simp only [rawSum,wordDot] at ih ⊢
      rw [ih]
      unfold val4
      ring

/-- A seed plus at most four bounded word-product contributions fits three words. -/
theorem comba_column_bound (seed a b c d : Nat) (hs : seed < 2 * B ^ 2)
    (ha : a ≤ 32 * B ^ 2) (hb : b ≤ 32 * B ^ 2)
    (hc : c ≤ 32 * B ^ 2) (hd : d ≤ 32 * B ^ 2) :
    seed + a + b + c + d < B ^ 3 := by
  norm_num [B] at *
  omega

#print axioms word_dot_bound
#print axioms word_dot_convolution
#print axioms comba_column_bound
end UdonVerify.ProductBlock
