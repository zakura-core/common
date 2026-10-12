import MontgomeryCommon
import Mathlib.Tactic.LinearCombination

open Aeneas Std

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] UScalar.cMax UScalar.ofNat

/-- A carry chain, allowing a one-word incoming carry. -/
theorem flag_chain_identity (a0 a1 a2 a3 b0 b1 b2 b3 incoming
    r0 r1 r2 r3 c0 c1 c2 c3 : Nat)
    (h0 : r0+B*c0 = a0+b0+incoming)
    (h1 : r1+B*c1 = a1+b1+c0)
    (h2 : r2+B*c2 = a2+b2+c1)
    (h3 : r3+B*c3 = a3+b3+c2) :
    r0+B*r1+B^2*r2+B^3*r3+R*c3 =
      a0+B*a1+B^2*a2+B^3*a3 + (b0+B*b1+B^2*b2+B^3*b3) + incoming := by
  unfold R
  linear_combination h0+B*h1+B^2*h2+B^3*h3

/-- Separate low and high product chains still accumulate the exact product. -/
theorem split_product_row_identity
    (a b old low high s0 s1 s2 s3 s4 n1 n2 n3 n4 carry : Nat)
    (hproduct : low+B*high = a*b)
    (hlow : s0+B*s1+B^2*s2+B^3*s3+R*s4 = old+low)
    (hhigh : n1+B*n2+B^2*n3+B^3*n4+R*carry =
      s1+B*s2+B^2*s3+B^3*s4+high) :
    s0+B*n1+B^2*n2+B^3*n3+R*n4+B*R*carry = old+a*b := by
  unfold R at *
  linear_combination hlow+B*hhigh+hproduct

/-- One schoolbook row cannot overflow its five-word accumulator. -/
theorem product_row_lt (a old b : Nat) (ha : a < R) (hold : old < R) (hb : b < B) :
    old+a*b < B*R := by
  have hab := Nat.mul_le_mul (Nat.le_pred_of_lt ha) (Nat.le_pred_of_lt hb)
  norm_num [B,R,Nat.pred_eq_sub_one] at *
  nlinarith only [hab,hold]

/-- The CIOS invariant bounds the full product-plus-modulus row before shifting. -/
theorem cancelled_row_lt (a p old b q : Nat)
    (hold : old < a+p) (hb : b < B) (hq : q < B) :
    old+a*b+q*p < B*(a+p) := by
  have hab := Nat.mul_le_mul_left a (Nat.succ_le_of_lt hb)
  have hqp := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hq)
  nlinarith only [hold,hab,hqp]

/-- After low-word cancellation, its carry is exactly whether the old word was nonzero. -/
theorem cancelled_low_carry (lhs low : U64)
    (hcancel : (lhs.val+low.val)%B = 0) :
    lhs.val+low.val = B*(lhs != 0#u64).toNat := by
  by_cases hz : lhs = 0#u64
  · subst lhs
    have hlow : low.val = 0 := by
      have hb := low.hmax
      norm_num [B,UScalar.max,UScalarTy.U64_numBits_eq] at hcancel hb
      omega
    simp [hlow]
  · have hlhs : 0 < lhs.val := by scalar_tac
    have hb0 := lhs.hmax
    have hb1 := low.hmax
    have hflag : (lhs != 0#u64) = true := by simpa only [bne_iff_ne] using hz
    rw [hflag]
    simp only [Bool.toNat_true, mul_one]
    norm_num [B,UScalar.max,UScalarTy.U64_numBits_eq] at *
    omega

/-- Splitting the modulus row leaves both shifted carry chains exact. -/
theorem split_modulus_low_identity
    (s0 s1 s2 s3 s4 p0 p1 q ql0 qh0 ql1 qh1 low high bit
      t1 t2 t3 t4 carryLow : Nat)
    (hproduct0 : ql0+B*qh0 = q*p0)
    (hproduct1 : ql1+B*qh1 = q*p1)
    (hcancel : s0+ql0 = B*bit)
    (hshift : low+B*high = q*2^62)
    (hlow : t1+B*t2+B^2*t3+B^3*t4+R*carryLow =
      s1+B*s2+B^2*s3+B^3*s4+ql1+B^2*low+bit) :
    B*(t1+B*t2+B^2*t3+B^3*t4)+B*R*carryLow+
      B*(qh0+B*qh1+B^3*high) =
      s0+B*s1+B^2*s2+B^3*s3+R*s4 + q*(p0+B*p1+B^3*2^62) := by
  unfold R at *
  linear_combination B*hlow+hproduct0+B*hproduct1-hcancel+B^3*hshift

/-- Both split modulus chains compose into the exact cancelled row. -/
theorem split_modulus_row_identity
    (s0 s1 s2 s3 s4 p0 p1 q ql0 qh0 ql1 qh1 low high bit
      t1 t2 t3 t4 carryLow n0 n1 n2 n3 carryHigh : Nat)
    (hproduct0 : ql0+B*qh0 = q*p0)
    (hproduct1 : ql1+B*qh1 = q*p1)
    (hcancel : s0+ql0 = B*bit)
    (hshift : low+B*high = q*2^62)
    (hlow : t1+B*t2+B^2*t3+B^3*t4+R*carryLow =
      s1+B*s2+B^2*s3+B^3*s4+ql1+B^2*low+bit)
    (hhigh : n0+B*n1+B^2*n2+B^3*n3+R*carryHigh =
      t1+B*t2+B^2*t3+B^3*t4+qh0+B*qh1+B^3*high) :
    B*(n0+B*n1+B^2*n2+B^3*n3)+B*R*(carryLow+carryHigh) =
      s0+B*s1+B^2*s2+B^3*s3+R*s4 + q*(p0+B*p1+B^3*2^62) := by
  unfold R at *
  linear_combination B*hlow+B*hhigh+hproduct0+B*hproduct1-hcancel+B^3*hshift

end UdonVerify
