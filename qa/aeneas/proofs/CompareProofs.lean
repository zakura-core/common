import Common

open Aeneas Std Result
open zakura_udon.field.pasta.word

namespace UdonVerify
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def orderingRel (o : Ordering) (x y : Nat) : Prop :=
  match o with
  | .lt => x < y
  | .eq => x = y
  | .gt => y < x

def prefix4 (a : A4) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => a[0]!.val
  | 2 => a[0]!.val + B*a[1]!.val
  | 3 => a[0]!.val + B*a[1]!.val + B^2*a[2]!.val
  | _ => val4 a

theorem compare_loop_unfold (lhs rhs : A4) (index : Usize) :
    compare_limbs_loop lhs rhs index = (do
      let r ← compare_limbs_loop.body lhs rhs index
      match r with
      | .done r => ok r
      | .cont i => compare_limbs_loop lhs rhs i) := by
  unfold compare_limbs_loop
  rw [loop]
  congr 1
  funext r
  cases r <;> rfl

@[step]
theorem compare_loop_zero (lhs rhs : A4) :
    compare_limbs_loop lhs rhs 0#usize ⦃ o => orderingRel o 0 0 ⦄ := by
  rw [compare_loop_unfold]
  unfold compare_limbs_loop.body
  simp [orderingRel]

@[step]
theorem compare_loop_1 (lhs rhs : A4) :
    compare_limbs_loop lhs rhs 1#usize ⦃ o =>
      orderingRel o (prefix4 lhs 1) (prefix4 rhs 1) ⦄ := by
  rw [compare_loop_unfold]
  unfold compare_limbs_loop.body
  simp only [show (1#usize) > 0#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step as ⟨index, hindex⟩
  have hindexeq : index = 0#usize := by scalar_tac
  subst index
  step as ⟨l, hl⟩
  step as ⟨r, hr⟩
  split
  · simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac
  · split
    · simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac
    · try simp only [bind_ok]
      step with compare_loop_zero as ⟨o, ho⟩
      cases o <;> simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac

@[step]
theorem compare_loop_2 (lhs rhs : A4) :
    compare_limbs_loop lhs rhs 2#usize ⦃ o =>
      orderingRel o (prefix4 lhs 2) (prefix4 rhs 2) ⦄ := by
  rw [compare_loop_unfold]
  unfold compare_limbs_loop.body
  simp only [show (2#usize) > 0#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step as ⟨index, hindex⟩
  have hindexeq : index = 1#usize := by scalar_tac
  subst index
  step as ⟨l, hl⟩
  step as ⟨r, hr⟩
  split
  · simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac
  · split
    · simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac
    · try simp only [bind_ok]
      step with compare_loop_1 as ⟨o, ho⟩
      cases o <;> simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac

@[step]
theorem compare_loop_3 (lhs rhs : A4) :
    compare_limbs_loop lhs rhs 3#usize ⦃ o =>
      orderingRel o (prefix4 lhs 3) (prefix4 rhs 3) ⦄ := by
  rw [compare_loop_unfold]
  unfold compare_limbs_loop.body
  simp only [show (3#usize) > 0#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step as ⟨index, hindex⟩
  have hindexeq : index = 2#usize := by scalar_tac
  subst index
  step as ⟨l, hl⟩
  step as ⟨r, hr⟩
  split
  · simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac
  · split
    · simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac
    · try simp only [bind_ok]
      step with compare_loop_2 as ⟨o, ho⟩
      cases o <;> simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac

@[step]
theorem compare_loop_4 (lhs rhs : A4) :
    compare_limbs_loop lhs rhs 4#usize ⦃ o =>
      orderingRel o (prefix4 lhs 4) (prefix4 rhs 4) ⦄ := by
  rw [compare_loop_unfold]
  unfold compare_limbs_loop.body
  simp only [show (4#usize) > 0#usize from by decide, if_pos]
  try simp only [Std.bind_assoc]
  step as ⟨index, hindex⟩
  have hindexeq : index = 3#usize := by scalar_tac
  subst index
  step as ⟨l, hl⟩
  step as ⟨r, hr⟩
  split
  · simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac
  · split
    · simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac
    · try simp only [bind_ok]
      step with compare_loop_3 as ⟨o, ho⟩
      cases o <;> simp_all [orderingRel, prefix4, val4, B] <;> scalar_tac

@[step]
theorem compare_limbs_spec (lhs rhs : A4) :
    compare_limbs lhs rhs ⦃ o => orderingRel o (val4 lhs) (val4 rhs) ⦄ := by
  simpa only [compare_limbs, prefix4] using compare_loop_4 lhs rhs

#print axioms compare_limbs_spec

end UdonVerify
