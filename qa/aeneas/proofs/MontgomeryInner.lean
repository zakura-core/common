import MontgomeryCommon

open Aeneas Std Result
open udon_kernel_slice.field.pasta.montgomery

namespace UdonVerify
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
attribute [local reducible] UScalar.cMax UScalar.ofNat

abbrev A5 := Aeneas.Std.Array U64 5#usize

def val5 (a : A5) : Nat :=
  a[0]!.val + B*a[1]!.val + B^2*a[2]!.val + B^3*a[3]!.val + R*a[4]!.val

abbrev range64 (n : Usize) : core.ops.range.Range Usize := { start := n, «end» := 4#usize }

theorem next_usize_0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize (range64 0#usize) =
    ok (some 0#usize, range64 1#usize) := by
  have h := WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec
    (range64 0#usize) (by simp))
  rcases h with ⟨⟨opt, range'⟩, heq, hopt, hstart, hend⟩
  rcases range' with ⟨s, e⟩
  have hs : s = 1#usize := by scalar_tac
  have he : e = 4#usize := hend
  subst s
  subst e
  simpa [hopt, range64] using heq

theorem next_usize_1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize (range64 1#usize) =
    ok (some 1#usize, range64 2#usize) := by
  have h := WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec
    (range64 1#usize) (by simp))
  rcases h with ⟨⟨opt, range'⟩, heq, hopt, hstart, hend⟩
  rcases range' with ⟨s, e⟩
  have hs : s = 2#usize := by scalar_tac
  have he : e = 4#usize := hend
  subst s
  subst e
  simpa [hopt, range64] using heq

theorem next_usize_2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize (range64 2#usize) =
    ok (some 2#usize, range64 3#usize) := by
  have h := WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec
    (range64 2#usize) (by simp))
  rcases h with ⟨⟨opt, range'⟩, heq, hopt, hstart, hend⟩
  rcases range' with ⟨s, e⟩
  have hs : s = 3#usize := by scalar_tac
  have he : e = 4#usize := hend
  subst s
  subst e
  simpa [hopt, range64] using heq

theorem next_usize_3 : core.iter.range.IteratorRange.next core.iter.range.StepUsize (range64 3#usize) =
    ok (some 3#usize, range64 4#usize) := by
  have h := WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec
    (range64 3#usize) (by simp))
  rcases h with ⟨⟨opt, range'⟩, heq, hopt, hstart, hend⟩
  rcases range' with ⟨s, e⟩
  have hs : s = 4#usize := by scalar_tac
  have he : e = 4#usize := hend
  subst s
  subst e
  simpa [hopt, range64] using heq

theorem next_usize_4 : core.iter.range.IteratorRange.next core.iter.range.StepUsize (range64 4#usize) =
    ok (none, range64 4#usize) := by
  have h := WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec
    (range64 4#usize) (by simp))
  rcases h with ⟨⟨opt, range'⟩, heq, hopt, hrange⟩
  simpa [hopt, hrange] using heq

theorem cios_inner_unfold (iter : core.ops.range.Range Usize) (lhs : A4)
    (acc : A5) (rhs : U64) (carry : U64) :
    montgomery_multiply_loop0_loop0 iter lhs acc rhs carry = (do
      let flow ← montgomery_multiply_loop0_loop0.body lhs rhs iter acc carry
      match flow with
      | .done r => ok r
      | .cont (it, a, c) => montgomery_multiply_loop0_loop0 it lhs a rhs c) := by
  unfold montgomery_multiply_loop0_loop0
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done r => rfl
  | cont r => rcases r with ⟨it, a, c⟩; rfl

@[step]
theorem multiply_inner_spec (lhs : A4) (rhs : U64) (acc : A5) :
    montgomery_multiply_loop0_loop0 (range64 0#usize) lhs acc rhs 0#u64 ⦃ out carry =>
      out[4]! = acc[4]! ∧ val5 out + R*carry.val = val5 acc + val4 lhs*rhs.val ⦄ := by
  rw [cios_inner_unfold]
  unfold montgomery_multiply_loop0_loop0.body
  rw [next_usize_0]
  simp only [bind_ok]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a0, ha0⟩
  step +scalarTac -grind as ⟨l0, hl0⟩
  step -grind with slice_mac_identity as ⟨pair0, h0⟩
  rcases pair0 with ⟨lo0, carry0⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨acc0, hacc0⟩
  subst acc0
  try simp only [bind_ok]
  rw [cios_inner_unfold]
  unfold montgomery_multiply_loop0_loop0.body
  rw [next_usize_1]
  simp only [bind_ok]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a1, ha1⟩
  step +scalarTac -grind as ⟨l1, hl1⟩
  step -grind with slice_mac_identity as ⟨pair1, h1⟩
  rcases pair1 with ⟨lo1, carry1⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨acc1, hacc1⟩
  subst acc1
  try simp only [bind_ok]
  rw [cios_inner_unfold]
  unfold montgomery_multiply_loop0_loop0.body
  rw [next_usize_2]
  simp only [bind_ok]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a2, ha2⟩
  step +scalarTac -grind as ⟨l2, hl2⟩
  step -grind with slice_mac_identity as ⟨pair2, h2⟩
  rcases pair2 with ⟨lo2, carry2⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨acc2, hacc2⟩
  subst acc2
  try simp only [bind_ok]
  rw [cios_inner_unfold]
  unfold montgomery_multiply_loop0_loop0.body
  rw [next_usize_3]
  simp only [bind_ok]
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨a3, ha3⟩
  step +scalarTac -grind as ⟨l3, hl3⟩
  step -grind with slice_mac_identity as ⟨pair3, h3⟩
  rcases pair3 with ⟨lo3, carry3⟩
  try dsimp only
  try simp only [Std.bind_assoc]
  step +scalarTac -grind as ⟨acc3, hacc3⟩
  subst acc3
  try simp only [bind_ok]
  rw [cios_inner_unfold]
  unfold montgomery_multiply_loop0_loop0.body
  rw [next_usize_4]
  simp only [bind_ok, WP.spec_ok]
  simp_all [val5, val4]
  norm_num only [B, R] at *
  ring_nf at *
  omega

#print axioms multiply_inner_spec

end UdonVerify
