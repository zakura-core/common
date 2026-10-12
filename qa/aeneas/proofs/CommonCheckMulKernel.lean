import CommonFG62Arrays
import CommonInvHelpers.Funs

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

theorem inv_helpers_mask_eq :
    CommonInvHelpers.field.pasta.safegcd.MASK62 = ok 4611686018427387903#u64 := by
  have h : CommonInvHelpers.field.pasta.safegcd.MASK62 =
      CommonFG62.field.pasta.safegcd.MASK62 := by
    unfold CommonInvHelpers.field.pasta.safegcd.MASK62 CommonFG62.field.pasta.safegcd.MASK62
    rfl
  exact h.trans fg_mask_eq

def checkMulAccumulate (carry : I128) (digit factor : I64) : Result I128 := do
  let wideDigit ← lift (core.convert.num.FromI128I64.from digit)
  let wideFactor ← lift (core.convert.num.FromI128I64.from factor)
  let product ← wideDigit * wideFactor
  carry + product

@[step]
theorem check_mul_accumulate_spec (carry : I128) (digit factor : I64)
    (hc : |carry.val| ≤ 3) (hd : |digit.val| ≤ signedRadix) (hf : |factor.val| ≤ 2) :
    checkMulAccumulate carry digit factor ⦃ out =>
      out.val = carry.val + digit.val * factor.val ∧ |out.val| ≤ 2 * signedRadix + 3 ⦄ := by
  have hp : |digit.val * factor.val| ≤ 2 * signedRadix := by
    rw [abs_mul]
    nlinarith [abs_nonneg digit.val, abs_nonneg factor.val]
  have hsum := abs_add_le carry.val (digit.val * factor.val)
  have hbound : |carry.val + digit.val * factor.val| ≤ 2 * signedRadix + 3 := by omega
  have hprodRange := abs_le.mp hp
  have hsumRange := abs_le.mp hbound
  norm_num only [signedRadix] at hprodRange hsumRange
  unfold checkMulAccumulate
  simp only [lift, bind_ok]
  step +scalarTac -grind with I128.mul_spec as ⟨product, hproduct⟩
  simp only [core.convert.num.FromI128I64.from_val_eq] at hproduct
  step +scalarTac -grind with I128.add_spec as ⟨out, hout⟩
  rw [hout, hproduct]
  exact ⟨rfl, hbound⟩

@[step]
theorem check_mul_shift_spec (value : I128) (h : |value.val| ≤ 2 * signedRadix + 3) :
    value >>> 62#i32 ⦃ out => out.val = value.val / signedRadix ∧ |out.val| ≤ 3 ⦄ := by
  step -grind with I128.ShiftRight_IScalar_spec as ⟨out, hval, _⟩
  have hv : out.val = value.val / signedRadix := by
    simpa only [show (62#i32).toNat = 62 from by decide, Int.shiftRight_eq_div_pow,
      signedRadix, Nat.cast_pow, Nat.cast_ofNat] using hval
  refine ⟨hv, ?_⟩
  rw [hv, abs_le]
  have hb := abs_le.mp h
  norm_num only [signedRadix] at hb ⊢
  omega

def checkMulRound (a : Signed62) (alen : Usize) (factor : I64)
    (index : Usize) (carry : I128) (out : Signed62) : Result (Signed62 × I128 × Signed62) := do
  let next ← if index < alen then do
    let digit ← Array.index_usize a index
    checkMulAccumulate carry digit factor
    else ok carry
  let mask ← CommonInvHelpers.field.pasta.safegcd.MASK62
  let digit := UScalar.hcast .I64 (IScalar.hcast .U64 next &&& mask)
  let out1 ← Array.update out index digit
  let carry1 ← next >>> 62#i32
  ok (a, carry1, out1)

theorem check_mul_body_bridge (alen : Usize) (factor : I64)
    (iter : core.ops.range.Range Usize) (a : Signed62) (carry : I128) (out : Signed62) :
    CommonInvHelpers.field.pasta.safegcd.checks.mul_62_loop.body alen factor iter a carry out =
      (do let (item, next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
          match item with
          | none => ok (ControlFlow.done (a, carry, out))
          | some index => do
            let (a1, carry1, out1) ← checkMulRound a alen factor index carry out
            ok (ControlFlow.cont (next, a1, carry1, out1))) := by
  unfold CommonInvHelpers.field.pasta.safegcd.checks.mul_62_loop.body
    checkMulRound checkMulAccumulate
  simp only [lift, bind_ok, Std.bind_assoc, Std.uncurry]
  congr 1
  funext pair
  rcases pair with ⟨item, next⟩
  cases item with
  | none => rfl
  | some index =>
    simp only [Std.uncurry_apply_pair]
    split_ifs <;> simp only [bind_ok, Std.bind_assoc, lift, Std.uncurry_apply_pair]

#print axioms inv_helpers_mask_eq
#print axioms check_mul_accumulate_spec
#print axioms check_mul_shift_spec
#print axioms check_mul_body_bridge
end UdonVerify.CommonSigned62
