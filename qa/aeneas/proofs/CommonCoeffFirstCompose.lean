import CommonCoeffFirstPrefix
import CommonCoeffFirstColumns

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def firstCoeffInputCheck (e : Signed62) : Result Unit := do
  let order ← CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62 e 5#usize zero62 0#i64
  let nonnegative ← core.cmp.PartialEq.ne.trait_default
    CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering order Ordering.lt
  massert nonnegative

@[step]
theorem first_coeff_input_check_spec {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (e : Signed62) (hne : signed62Normalized e)
    (he : 0 ≤ signed62Value e)
    (hre : -2 * signed62Value params.modulus < signed62Value e ∧ signed62Value e < signed62Value params.modulus) :
    firstCoeffInputCheck e ⦃ out => out = () ⦄ := by
  obtain ⟨hd, htop⟩ := inv_coefficient_digit_bounds inst params e hne hre
  have hz : ∀ k : Fin 5, |zero62[k.val]!.val| ≤ signedRadix := by
    intro k
    rw [zero62_digit _ k.isLt]
    norm_num [signedRadix]
  unfold firstCoeffInputCheck
  apply WP.spec_bind (check_mul_cmp_62_spec e 5#usize zero62 0#i64 (by decide) (by decide)
    hd hz (by intro _; exact htop) (by rw [zero62_digit 4 (by decide)]; decide))
  intro order horder
  have hnot : order ≠ .lt := by
    have htags := integer_compare_tags _ _ order horder
    rw [show (5#usize).val = 5 from by decide, active62_value_five,
      show (0#i64).val = 0 from by decide, zero_mul] at htags
    intro hlt
    have := htags.1.mp hlt
    omega
  cases order <;>
    simp_all [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering,
      CommonInvHelpers.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq, lift, Bind.bind,
      massert, WP.spec_ok]

def updateDEFirstColumns {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (e : Signed62)
    (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) : Result (Signed62 × Signed62) := do
  firstCoeffInputCheck e
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst e (CommonInvHelpers.toStr "e")
  let p ← firstCoeffPrefix inst e t
  let c1 ← firstCoeffColumn1 t e[1]! params.modulus[1]! p.md p.me p.cd p.ce
  let c2 ← firstCoeffColumn2 t e[2]! params.modulus[2]! p.md p.me c1.carryD c1.carryE
  let c3 ← firstCoeffColumn3 t e[3]! params.modulus[3]! p.md p.me c2.carryD c2.carryE
  let c4 ← firstCoeffColumn4 t e[4]! params.modulus[4]! p.md p.me c3.carryD c3.carryE
  let dtail ← fgRowTail c4.carryD
  let etail ← fgRowTail c4.carryE
  let dOut := storeCoeffRow zero62 c1.accD c2.accD c3.accD c4.accD dtail
  let eOut := storeCoeffRow zero62 c1.accE c2.accE c3.accE c4.accE etail
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst dOut (CommonInvHelpers.toStr "new d")
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst eOut (CommonInvHelpers.toStr "new e")
  ok (dOut, eOut)

theorem update_de_first_columns_bridge {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (e : Signed62)
    (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) :
    CommonInvHelpers.field.pasta.safegcd.update_de_62_first inst e t = updateDEFirstColumns params e t := by
  unfold CommonInvHelpers.field.pasta.safegcd.update_de_62_first updateDEFirstColumns firstCoeffInputCheck
    firstCoeffPrefix firstCoeffColumn1 firstCoeffColumn2 firstCoeffColumn3 firstCoeffColumn4
    fgZeroTerm coeffModTerm fgRowTail firstResidueDigit storeCoeffRow fgRowDigit zero62
  rw [params.mu_eq, params.modulus_eq]
  simp (config := { maxSteps := 1000000 }) [lift, Bind.bind, bind_ok, Std.bind_assoc,
    fg_index_eq, fg_update_eq, inv_helpers_mask_eq, core.num.U64.wrapping_mul]

#print axioms first_coeff_input_check_spec
#print axioms update_de_first_columns_bridge
end UdonVerify.CommonSigned62
