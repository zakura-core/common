import NativeBasics

open Aeneas Std Result

namespace UdonVerify.Native
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

abbrev fullMask : U64 := 18446744073709551615#u64

theorem and_zero (x : U64) : x &&& (0#u64) = 0#u64 := by
  apply UScalar.eq_of_val_eq
  change x.val &&& 0 = 0
  exact Nat.and_zero x.val

theorem and_full (x : U64) : x &&& fullMask = x := by
  apply UScalar.eq_of_val_eq
  change x.val &&& (2^64-1) = x.val
  rw [Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  scalar_tac

theorem wrapping_neg_zero : NativeField.core.num.U64.wrapping_neg 0#u64 = ok (0#u64) := by
  rfl

theorem wrapping_neg_one : NativeField.core.num.U64.wrapping_neg 1#u64 = ok fullMask := by
  rfl

@[step]
theorem wrapping_neg_bit_spec (borrow : U64) (hb : borrow.val ≤ 1) :
    NativeField.core.num.U64.wrapping_neg borrow ⦃ mask =>
      mask = if borrow.val=0 then 0#u64 else fullMask ⦄ := by
  by_cases hzero : borrow=0#u64
  · subst borrow
    rw [wrapping_neg_zero]
    simp
  · have hone : borrow=1#u64 := by scalar_tac
    subst borrow
    rw [wrapping_neg_one]
    simp

theorem val4_zero_iff (limbs : A4) : val4 limbs=0 ↔
    limbs[0]!.val=0 ∧ limbs[1]!.val=0 ∧ limbs[2]!.val=0 ∧ limbs[3]!.val=0 := by
  unfold val4
  norm_num only [B]
  omega

theorem or4_zero_iff (a b c d : U64) : ((a ||| b) ||| c) ||| d = 0#u64 ↔
    a.val=0 ∧ b.val=0 ∧ c.val=0 ∧ d.val=0 := by
  constructor
  · intro h
    have heq : ((a.val ||| b.val) ||| c.val) ||| d.val=0 := congrArg UScalar.val h
    have h0 : a.val ≤ a.val ||| b.val := Nat.left_le_or
    have h1 : b.val ≤ a.val ||| b.val := Nat.right_le_or
    have h2 : a.val ||| b.val ≤ (a.val ||| b.val) ||| c.val := Nat.left_le_or
    have h3 : c.val ≤ (a.val ||| b.val) ||| c.val := Nat.right_le_or
    have h4 : (a.val ||| b.val) ||| c.val ≤ ((a.val ||| b.val) ||| c.val) ||| d.val := Nat.left_le_or
    have h5 : d.val ≤ ((a.val ||| b.val) ||| c.val) ||| d.val := Nat.right_le_or
    omega
  · rintro ⟨ha,hb,hc,hd⟩
    apply UScalar.eq_of_val_eq
    simp only [UScalar.val_or]
    change ((a.val ||| b.val) ||| c.val) ||| d.val=0
    simp [ha,hb,hc,hd]

#print axioms wrapping_neg_bit_spec
#print axioms and_full

end UdonVerify.Native
