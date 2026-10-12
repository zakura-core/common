import CommonCoeffTerminalColumns

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def updateDOnlyColumns {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (d e : Signed62) (u v : I64) : Result Signed62 := do
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst d (CommonInvHelpers.toStr "d")
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst e (CommonInvHelpers.toStr "e")
  let p ← terminalCoeffPrefix inst d e u v
  let c1 ← terminalCoeffColumn1 u v d[1]! e[1]! params.modulus[1]! p.md p.cd
  let c2 ← terminalCoeffColumn2 u v d[2]! e[2]! params.modulus[2]! p.md c1.carryD
  let c3 ← terminalCoeffColumn3 u v d[3]! e[3]! params.modulus[3]! p.md c2.carryD
  let c4 ← terminalCoeffColumn4 u v d[4]! e[4]! params.modulus[4]! p.md c3.carryD
  let tail ← fgRowTail c4.carryD
  let out := storeCoeffRow d c1.accD c2.accD c3.accD c4.accD tail
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst out (CommonInvHelpers.toStr "new d")
  ok out

theorem update_d_only_columns_bridge {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (d e : Signed62) (u v : I64) :
    CommonInvHelpers.field.pasta.safegcd.update_d_only_62 inst d e u v = updateDOnlyColumns params d e u v := by
  unfold CommonInvHelpers.field.pasta.safegcd.update_d_only_62 updateDOnlyColumns terminalCoeffPrefix
    terminalCoeffColumn1 terminalCoeffColumn2 terminalCoeffColumn3 terminalCoeffColumn4
    coeffSignStart fgRowTerm coeffModTerm fgRowTail coeffCorrectWord coeffResidueDigit coeffResidue
    storeCoeffRow fgRowDigit
  rw [params.mu_eq, params.modulus_eq]
  simp (config := { maxSteps := 1000000 }) [lift, Bind.bind, bind_ok, Std.bind_assoc,
    fg_index_eq, fg_update_eq, coeff_sign_shift_eq, inv_helpers_mask_eq,
    core.num.U64.wrapping_add, core.num.U64.wrapping_mul, core.num.I64.wrapping_sub]

#print axioms update_d_only_columns_bridge
end UdonVerify.CommonSigned62
