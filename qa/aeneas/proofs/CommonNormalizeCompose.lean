import CommonNormalizeAdd
import CommonNormalizeNegate
import CommonNormalizeChecks

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def normalizeColumns {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (r : Signed62) (sign : I64) : Result Signed62 := do
  CommonInvHelpers.field.pasta.safegcd.checks.assert_coeff_range inst r (CommonInvHelpers.toStr "normalize input")
  let a ← normalizeAdd r params.modulus
  let n ← normalizeNegateAll a sign
  let c ← normalizeCarry n
  let a2 ← normalizeAdd c params.modulus
  let out ← normalizeCarry a2
  normalizeCanonicalCheck out
  firstCoeffInputCheck out
  normalizeReducedCheck out params.modulus
  ok out

theorem normalize_columns_bridge {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (r : Signed62) (sign : I64) :
    CommonInvHelpers.field.pasta.safegcd.normalize_62 inst r sign = normalizeColumns params r sign := by
  unfold CommonInvHelpers.field.pasta.safegcd.normalize_62 normalizeColumns normalizeAdd normalizeNegateAll
    normalizeCarry normalizeCanonicalCheck firstCoeffInputCheck normalizeReducedCheck
    make62 normalizeDigit zero62
  rw [params.modulus_eq]
  simp (config := { maxSteps := 1000000 }) [lift, Bind.bind, bind_ok, Std.bind_assoc,
    fg_index_eq, inv_helpers_mask_eq, coeff_sign_shift_eq,
    show UScalar.hcast .I64 4611686018427387903#u64 = 4611686018427387903#i64 from by decide]

#print axioms normalize_columns_bridge
end UdonVerify.CommonSigned62
