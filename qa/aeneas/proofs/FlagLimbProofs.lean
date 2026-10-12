import Common
import WordPrimitives

open Aeneas Std Result
open zakura_udon.field.pasta.word

namespace UdonVerify

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- The four flag-carried additions preserve the exact 256-bit integer sum. -/
@[step]
theorem carry_add_limbs_spec (lhs rhs : A4) :
    carry_add_limbs lhs rhs ⦃ out =>
      val4 out.1 + R * out.2.toNat = val4 lhs + val4 rhs ⦄ := by
  unfold carry_add_limbs
  step*
  all_goals simp_all [val4, R, B]
  all_goals scalar_tac

/-- The four flag-carried subtractions preserve the exact 256-bit difference. -/
@[step]
theorem borrow_sub_limbs_spec (lhs rhs : A4) :
    borrow_sub_limbs lhs rhs ⦃ out =>
      val4 out.1 + val4 rhs = val4 lhs + R * out.2.toNat ⦄ := by
  unfold borrow_sub_limbs
  step*
  all_goals simp_all [val4, R, B]
  all_goals scalar_tac

#print axioms carry_add_limbs_spec
#print axioms borrow_sub_limbs_spec

end UdonVerify
