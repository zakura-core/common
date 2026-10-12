import Common

open Aeneas Std Result
open zakura_udon.field.pasta.word

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem add_loop_unfold (lhs rhs result : A4) (carry : U64) (index : Usize) :
    add_limbs_loop lhs rhs result carry index = (do
      let r ← add_limbs_loop.body lhs rhs result carry index
      match r with
      | .done r => ok r
      | .cont (a, c, i) => add_limbs_loop lhs rhs a c i) := by
  unfold add_limbs_loop
  rw [loop]
  congr 1
  funext r
  cases r with
  | done r => rfl
  | cont r => rcases r with ⟨a, c, i⟩; rfl

@[step]
theorem add_limbs_spec (lhs rhs : A4) :
    add_limbs lhs rhs ⦃ out carry =>
      carry.val ≤ 1 ∧ val4 out + R * carry.val = val4 lhs + val4 rhs ⦄ := by
  unfold add_limbs
  rw [add_loop_unfold]
  unfold add_limbs_loop.body
  simp only [show (0#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step as ⟨l0, hl0⟩
  step as ⟨r0, hr0⟩
  step with kernel_adc_identity as ⟨pair0, h0⟩
  rcases pair0 with ⟨lo0, carry0⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step as ⟨a0, ha0⟩
  step as ⟨index0, hindex0⟩
  have hindexeq0 : index0 = 1#usize := by scalar_tac
  subst index0
  subst a0
  try simp only [bind_ok]
  rw [add_loop_unfold]
  unfold add_limbs_loop.body
  simp only [show (1#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step as ⟨l1, hl1⟩
  step as ⟨r1, hr1⟩
  step with kernel_adc_identity as ⟨pair1, h1⟩
  rcases pair1 with ⟨lo1, carry1⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step as ⟨a1, ha1⟩
  step as ⟨index1, hindex1⟩
  have hindexeq1 : index1 = 2#usize := by scalar_tac
  subst index1
  subst a1
  try simp only [bind_ok]
  rw [add_loop_unfold]
  unfold add_limbs_loop.body
  simp only [show (2#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step as ⟨l2, hl2⟩
  step as ⟨r2, hr2⟩
  step with kernel_adc_identity as ⟨pair2, h2⟩
  rcases pair2 with ⟨lo2, carry2⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step as ⟨a2, ha2⟩
  step as ⟨index2, hindex2⟩
  have hindexeq2 : index2 = 3#usize := by scalar_tac
  subst index2
  subst a2
  try simp only [bind_ok]
  rw [add_loop_unfold]
  unfold add_limbs_loop.body
  simp only [show (3#usize) < 4#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step as ⟨l3, hl3⟩
  step as ⟨r3, hr3⟩
  step with kernel_adc_identity as ⟨pair3, h3⟩
  rcases pair3 with ⟨lo3, carry3⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step as ⟨a3, ha3⟩
  step as ⟨index3, hindex3⟩
  have hindexeq3 : index3 = 4#usize := by scalar_tac
  subst index3
  subst a3
  try simp only [bind_ok]
  rw [add_loop_unfold]
  unfold add_limbs_loop.body
  simp only [show ¬ ((4#usize) < 4#usize) from by decide, if_neg, bind_ok, WP.spec_ok]
  simp_all [val4, R, B]
  all_goals scalar_tac

#print axioms add_limbs_spec

end UdonVerify
