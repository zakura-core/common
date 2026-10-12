import CommonCoeffSpecialMath

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def firstCoeffPrefix {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2) : Result CoeffPrefix := do
  let cd ← fgZeroTerm t.v e[0]!
  let ce ← fgZeroTerm t.r e[0]!
  let mu ← inst.MU
  let md ← CommonInvHelpers.core.num.I64.wrapping_neg (firstResidueDigit mu cd)
  let me ← CommonInvHelpers.core.num.I64.wrapping_neg (firstResidueDigit mu ce)
  let modulus ← inst.MODULUS_62
  let modD0 ← coeffModTerm modulus[0]! md
  let cd0 ← cd + modD0
  let modE0 ← coeffModTerm modulus[0]! me
  let ce0 ← ce + modE0
  massert (IScalar.hcast .U64 cd0 &&& 4611686018427387903#u64 = 0#u64)
  massert (IScalar.hcast .U64 ce0 &&& 4611686018427387903#u64 = 0#u64)
  let cdCarry0 ← cd0 >>> 62#i32
  let ceCarry0 ← ce0 >>> 62#i32
  ok ⟨md, me, cdCarry0, ceCarry0⟩

theorem first_coeff_prefix_bridge {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (hne : signed62Normalized e) (he : 0 ≤ signed62Value e)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix) :
    firstCoeffPrefix inst e t = coeffPrefix inst zero62 e t := by
  have he4 : 0 ≤ e[4]!.val := by
    have := signed62_sign_iff e hne
    omega
  unfold firstCoeffPrefix coeffPrefix
  simp only [zero62_digit 4 (by decide), zero62_digit 0 (by decide),
    coeff_sign_nonnegative_eq t.u t.v 0#i64 e[4]! huv (by decide) he4,
    coeff_sign_nonnegative_eq t.q t.r 0#i64 e[4]! hqr (by decide) he4,
    bind_ok, fg_row_zero_left_eq, first_correction_eq]

@[step]
theorem first_coeff_prefix_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (e : Signed62) (t : CommonInvHelpers.field.pasta.safegcd.Trans2x2)
    (hne : signed62Normalized e) (he : 0 ≤ signed62Value e)
    (hre : -2 * signed62Value params.modulus < signed62Value e ∧ signed62Value e < signed62Value params.modulus)
    (huv : |t.u.val| + |t.v.val| ≤ signedRadix) (hqr : |t.q.val| + |t.r.val| ≤ signedRadix) :
    firstCoeffPrefix inst e t ⦃ out => CoeffPrefixPost params zero62 e t out ⦄ := by
  rw [first_coeff_prefix_bridge inst e t hne he huv hqr]
  apply coeff_prefix_spec inst params zero62 e t zero62_normalized hne _ hre huv hqr
  rw [zero62_value]
  have := params.positive
  constructor <;> omega

#print axioms first_coeff_prefix_bridge
#print axioms first_coeff_prefix_spec
end UdonVerify.CommonSigned62
