import CommonCheckMulInvariant

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem check_mul_loop_unfold (iter : core.ops.range.Range Usize) (a : Signed62) (alen : Usize)
    (factor : I64) (carry : I128) (out : Signed62) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_62_loop iter a alen factor carry out =
      (do let flow ← CommonInvHelpers.field.pasta.safegcd.checks.mul_62_loop.body alen factor iter a carry out
          match flow with
          | .done result => ok result
          | .cont (next, a1, carry1, out1) =>
            CommonInvHelpers.field.pasta.safegcd.checks.mul_62_loop next a1 alen factor carry1 out1) := by
  unfold CommonInvHelpers.field.pasta.safegcd.checks.mul_62_loop
  rw [loop]
  congr 1
  funext flow
  cases flow with
  | done result => rfl
  | cont state => rcases state with ⟨next, a1, carry1, out1⟩; rfl

@[step]
theorem check_mul_loop_spec (a : Signed62) (alen : Usize) (factor : I64)
    (ha : ∀ k : Fin 5, |a[k.val]!.val| ≤ signedRadix) (hf : |factor.val| ≤ 2)
    (iter : core.ops.range.Range Usize) (carry : I128) (out : Signed62)
    (hstart : iter.start.val ≤ 4) (hend : iter.end = 4#usize)
    (h : CheckMulInvariant a alen factor iter.start.val carry out) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_62_loop iter a alen factor carry out ⦃ result =>
      result.1 = a ∧ CheckMulInvariant a alen factor 4 result.2.1 result.2.2 ⦄ := by
  generalize hn : 4 - iter.start.val = n
  induction n using Nat.strong_induction_on generalizing iter carry out with
  | h n ih =>
    rw [check_mul_loop_unfold, check_mul_body_bridge]
    by_cases hlt : iter.start.val < iter.end.val
    · obtain ⟨⟨item, next⟩, hnext, hitem, hnextStart, hnextEnd⟩ :=
        WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_some_spec iter hlt)
      subst item
      rw [hnext]
      simp only [bind_ok, Std.bind_assoc, Std.uncurry_apply_pair]
      have hi : iter.start.val < 4 := by rw [hend] at hlt; exact hlt
      apply WP.spec_bind (check_mul_round_spec a alen factor iter.start carry out
        (by omega) h.carry_bound hf (ha ⟨iter.start.val, by omega⟩))
      intro result hr
      rcases result with ⟨a1, carry1, out1⟩
      rcases hr with ⟨acc, hacc, ha1, hcarry, hbound, hout1⟩
      dsimp only at ha1 hcarry hbound hout1
      subst a1
      subst out1
      have hadvance := check_mul_invariant_advance a alen factor iter.start carry carry1 acc out
        hi h hacc hcarry hbound
      have hnextInvariant : CheckMulInvariant a alen factor next.start.val carry1
          (out.set iter.start (fgRowDigit acc)) := by
        simpa only [hnextStart] using hadvance
      have hnextStartBound : next.start.val ≤ 4 := by rw [hnextStart]; omega
      have hnextEndEq : next.end = 4#usize := by rw [hnextEnd, hend]
      simp only [Std.uncurry_apply_pair, bind_ok]
      exact ih (4 - next.start.val) (by rw [hnextStart]; omega) next carry1
        (out.set iter.start (fgRowDigit acc)) hnextStartBound hnextEndEq hnextInvariant rfl
    · obtain ⟨⟨item, next⟩, hnext, hitem, hnextEq⟩ :=
        WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec iter (by omega))
      subst item
      subst next
      rw [hnext]
      simp only [bind_ok, Std.uncurry_apply_pair, WP.spec_ok]
      have hfour : iter.start.val = 4 := by
        rw [hend, show (4#usize).val = 4 from by decide] at hlt
        omega
      simpa only [hfour, true_and] using h

#print axioms check_mul_loop_unfold
#print axioms check_mul_loop_spec
end UdonVerify.CommonSigned62
