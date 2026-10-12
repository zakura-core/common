import CommonCoeffFlat
import CommonCoeffPrefix
import CommonCoeffColumns
import CommonCoeffStore

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def updateDEColumns {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (d e : Signed62)
    (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) : Result (Signed62 × Signed62) := do
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst d (CommonInvHelpers.toStr "d")
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst e (CommonInvHelpers.toStr "e")
  let p ← coeffPrefix inst d e t
  let c1 ← coeffColumn1 t d[1]! e[1]! params.modulus[1]! p.md p.me p.cd p.ce
  let c2 ← coeffColumn2 t d[2]! e[2]! params.modulus[2]! p.md p.me c1.carryD c1.carryE
  let c3 ← coeffColumn3 t d[3]! e[3]! params.modulus[3]! p.md p.me c2.carryD c2.carryE
  let c4 ← coeffColumn4 t d[4]! e[4]! params.modulus[4]! p.md p.me c3.carryD c3.carryE
  let dtail ← fgRowTail c4.carryD
  let etail ← fgRowTail c4.carryE
  let dOut := storeCoeffRow d c1.accD c2.accD c3.accD c4.accD dtail
  let eOut := storeCoeffRow e c1.accE c2.accE c3.accE c4.accE etail
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst dOut (CommonInvHelpers.toStr "new d")
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst eOut (CommonInvHelpers.toStr "new e")
  ok (dOut, eOut)

theorem update_de_columns_bridge {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (d e : Signed62)
    (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) :
    updateDEFlat inst d e t = updateDEColumns params d e t := by
  unfold updateDEFlat updateDEColumns coeffPrefix coeffColumn1 coeffColumn2 coeffColumn3 coeffColumn4 storeCoeffRow
  rw [params.mu_eq, params.modulus_eq]
  simp only [bind_ok, Std.bind_assoc]

#print axioms update_de_columns_bridge
end UdonVerify.CommonSigned62
