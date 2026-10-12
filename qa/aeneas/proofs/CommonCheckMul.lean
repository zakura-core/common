import CommonCheckMulLoop
import CommonFG62Sparse

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def checkMulFinish (a : Signed62) (alen : Usize) (factor : I64) (carry : I128)
    (out : Signed62) : Result Signed62 := do
  let acc ← if 4#usize < alen then do
    let digit ← Array.index_usize a 4#usize
    checkMulAccumulate carry digit factor
    else ok carry
  let last ← fgRowTail acc
  let result ← Array.update out 4#usize last
  ok result

theorem check_mul_root_bridge (a : Signed62) (alen : Usize) (factor : I64) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_62 a alen factor =
      (do let (a1, carry, out) ← CommonInvHelpers.field.pasta.safegcd.checks.mul_62_loop
            { start := 0#usize, «end» := 4#usize } a alen factor 0#i128
            (Array.repeat 5#usize 0#i64)
          checkMulFinish a1 alen factor carry out) := by
  unfold CommonInvHelpers.field.pasta.safegcd.checks.mul_62 checkMulFinish
    checkMulAccumulate fgRowTail
  simp only [lift, bind_ok, Std.bind_assoc, Std.uncurry_apply_pair]

theorem check_mul_final_bound (a : Signed62) (alen : Usize) (factor : I64) (carry acc : I128)
    (hlen : alen.val ≤ 5) (hc : |carry.val| ≤ 3) (hf : |factor.val| ≤ 2)
    (ht : alen.val = 5 → |a[4]!.val| ≤ 256)
    (hacc : acc.val = carry.val + (if 4 < alen.val then a[4]!.val * factor.val else 0)) :
    |acc.val| ≤ 515 := by
  by_cases hlast : 4 < alen.val
  · have htop := ht (by omega)
    have hp : |a[4]!.val * factor.val| ≤ 512 := by
      rw [abs_mul]
      nlinarith [abs_nonneg a[4]!.val, abs_nonneg factor.val]
    have hs := abs_add_le carry.val (a[4]!.val * factor.val)
    rw [hacc, if_pos hlast]
    omega
  · rw [hacc, if_neg hlast, add_zero]
    omega

@[step]
theorem check_mul_finish_spec (a : Signed62) (alen : Usize) (factor : I64) (carry : I128)
    (out : Signed62) (hlen : alen.val ≤ 5) (hf : |factor.val| ≤ 2)
    (ha : ∀ k : Fin 5, |a[k.val]!.val| ≤ signedRadix)
    (ht : alen.val = 5 → |a[4]!.val| ≤ 256)
    (h : CheckMulInvariant a alen factor 4 carry out) :
    checkMulFinish a alen factor carry out ⦃ result =>
      signed62Normalized result ∧ signed62Value result = factor.val * active62Value a alen.val ⦄ := by
  unfold checkMulFinish
  apply WP.spec_bind (check_mul_select_spec a alen 4#usize factor carry (by decide)
    h.carry_bound hf (ha ⟨4, by decide⟩))
  intro acc hacc
  have haccValue : acc.val = carry.val + (if 4 < alen.val then a[4]!.val * factor.val else 0) := by
    simpa only [show (4#usize).val = 4 from by decide] using hacc.1
  have hb := check_mul_final_bound a alen factor carry acc hlen h.carry_bound hf ht haccValue
  apply WP.spec_bind (fg_row_tail_spec acc (by norm_num only [signedRadix]; omega))
  intro last hlast
  rw [fg_update_eq out 4#usize last (by decide)]
  simp only [bind_ok, WP.spec_ok]
  constructor
  · intro k
    rw [Array.getElem!_Nat_set_ne _ _ _ _ (by have := k.isLt; norm_num; omega)]
    exact h.normalized k k.isLt
  · rw [← active62_value_five]
    have hlastValue : active62Value (out.set 4#usize last) 5 =
        active62Value out 4 + signedRadix ^ 4 * acc.val := by
      simpa only [show (4#usize).val = 4 from by decide, hlast] using
        active62_set_succ out 4#usize last (by decide)
    rw [hlastValue, haccValue]
    have hn : min (4 + 1) alen.val = alen.val := Nat.min_eq_right hlen
    have hexpansion := active62_min_succ a alen.val 4
    rw [hn] at hexpansion
    rw [hexpansion]
    split_ifs <;> nlinarith only [h.value]

@[step]
theorem check_mul_62_spec (a : Signed62) (alen : Usize) (factor : I64)
    (hlen : alen.val ≤ 5) (hf : |factor.val| ≤ 2)
    (ha : ∀ k : Fin 5, |a[k.val]!.val| ≤ signedRadix)
    (ht : alen.val = 5 → |a[4]!.val| ≤ 256) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_62 a alen factor ⦃ result =>
      signed62Normalized result ∧ signed62Value result = factor.val * active62Value a alen.val ⦄ := by
  rw [check_mul_root_bridge]
  apply WP.spec_bind (check_mul_loop_spec a alen factor ha hf
    { start := 0#usize, «end» := 4#usize } 0#i128 (Array.repeat 5#usize 0#i64)
    (by decide) rfl (check_mul_invariant_initial a alen factor))
  intro result hr
  rcases result with ⟨a1, carry, out⟩
  rcases hr with ⟨ha1, hinvariant⟩
  dsimp only at ha1 hinvariant
  subst a1
  exact check_mul_finish_spec a alen factor carry out hlen hf ha ht hinvariant

#print axioms check_mul_root_bridge
#print axioms check_mul_final_bound
#print axioms check_mul_finish_spec
#print axioms check_mul_62_spec
end UdonVerify.CommonSigned62
