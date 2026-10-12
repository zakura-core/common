import CommonDivstepSentinel
open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

@[step]
theorem sentinel_word_spec (g : U64) (remaining : U32) (hr : remaining.val < 64) :
    (do let top ← core.num.U64.MAX <<< remaining
        ok (g ||| top)) ⦃ out => out=sentinelWord g remaining.val ⦄ := by
  step -grind with U64.ShiftLeft_spec as ⟨top,hval,hbv⟩
  apply U64.bv_eq_imp_eq
  change (g ||| top).bv = g.bv ||| (BitVec.allOnes 64 <<< remaining.val)
  rw [UScalar.bv_or,hbv]
  congr 2
  try decide

theorem u32_to_i64_value (value : U32) :
    (UScalar.hcast .I64 value).val = (value.val : Int) := by
  rw [UScalar.hcast_val_eq]
  change Int.bmod (value.val : Int) (2^64) = (value.val : Int)
  apply Arith.Int.bmod_pow2_eq_of_inBounds 63 <;> scalar_tac

def stripZeroState (eta : I64) (u v g : U64) (remaining : U32) :
    Result (I64 × U64 × U64 × U64 × U32 × U32) := do
  let top ← core.num.U64.MAX <<< remaining
  let sentinel ← lift (g ||| top)
  let zeros ← CommonDivsteps.core.num.U64.trailing_zeros sentinel
  let g1 ← g >>> zeros
  let u1 ← u <<< zeros
  let v1 ← v <<< zeros
  let z64 ← CommonDivsteps.I64.Insts.CoreConvertFromU32.from zeros
  let eta1 ← eta-z64
  let remaining1 ← remaining-zeros
  ok (eta1,u1,v1,g1,remaining1,zeros)

@[step]
theorem strip_zero_state_spec (eta : I64) (u v g : U64) (remaining : U32)
    (hr : 0 < remaining.val ∧ remaining.val ≤ 62)
    (he : -745 ≤ eta.val ∧ eta.val ≤ 745) :
    stripZeroState eta u v g remaining ⦃ out =>
      let zeros := out.2.2.2.2.2
      zeros.val = trailingZeros64 (sentinelWord g remaining.val) ∧
      zeros.val ≤ remaining.val ∧
      out.1.val = eta.val-(zeros.val:Int) ∧
      out.2.1.bv = u.bv <<< zeros.val ∧
      out.2.2.1.bv = v.bv <<< zeros.val ∧
      out.2.2.2.1.val = g.val/2^zeros.val ∧
      out.2.2.2.2.1.val = remaining.val-zeros.val ∧
      g.val%2^zeros.val=0 ∧
      (0 < out.2.2.2.2.1.val → out.2.2.2.1.val%2=1) ⦄ := by
  unfold stripZeroState
  step -grind with U64.ShiftLeft_spec as ⟨top,htval,htbv⟩
  have hsent : g ||| top=sentinelWord g remaining.val := by
    apply U64.bv_eq_imp_eq
    change (g ||| top).bv = g.bv ||| (BitVec.allOnes 64 <<< remaining.val)
    rw [UScalar.bv_or,htbv]
    congr 2
    try decide
  simp only [lift,bind_ok,hsent]
  step -grind with trailing_zeros_spec as ⟨zeros,hzeros⟩
  have hzbound : zeros.val ≤ remaining.val := by
    rw [hzeros]
    exact sentinel_count_bound g remaining.val (by omega)
  step -grind with U64.ShiftRight_spec as ⟨g1,hgval,hgbv⟩
  step -grind with U64.ShiftLeft_spec as ⟨u1,huval,hubv⟩
  step -grind with U64.ShiftLeft_spec as ⟨v1,hvval,hvbv⟩
  try simp only [CommonDivsteps.I64.Insts.CoreConvertFromU32.from,bind_ok]
  have hcast := u32_to_i64_value zeros
  step +scalarTac -grind with I64.sub_spec as ⟨eta1,heta⟩
  step +scalarTac -grind with U32.sub_spec as ⟨remaining1,hremaining⟩
  try simp only [WP.spec_ok]
  refine ⟨hzeros,hzbound,?_,hubv,hvbv,?_,hremaining,?_,?_⟩
  · rw [heta,hcast]
  · simpa only [Nat.shiftRight_eq_div_pow] using hgval
  · rw [hzeros]
    exact sentinel_low_bits g remaining.val
  · intro hpositive
    rw [hgval,Nat.shiftRight_eq_div_pow,hzeros]
    exact sentinel_odd_quotient g remaining.val (by omega) (by omega)

#print axioms sentinel_word_spec
#print axioms u32_to_i64_value
#print axioms strip_zero_state_spec
end UdonVerify.CommonSigned62
