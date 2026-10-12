import CommonInversionInvBridge
import CommonInversionFGBridge
import CommonInversionDivstepBridge
import CommonInversionDigitBounds
import CommonInversionRanges
import CommonInversionTerminationMath
import CommonInversionBezout

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

structure InversionParameters {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P) where
  helpers : InvHelperParameters (inversionHelperDict inst)
  r2 : Signed62
  r2_eq : inst.R2_62 = ok r2
  r2_normalized : signed62Normalized r2
  r2_range : 0 ≤ signed62Value r2 ∧ signed62Value r2 < signed62Value helpers.modulus
  r2_congruence : Int.ModEq (signed62Value helpers.modulus) (signed62Value r2) (2 ^ 512)
  odd : signed62Value helpers.modulus % 2 = 1
  large : signedRadix < signed62Value helpers.modulus

def inversionTrace (modulus x : Int) (batches : Nat) : State :=
  iterate (62 * batches) ⟨1, modulus, x⟩

structure InversionInvariant {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat)
    (f g d e : Signed62) (eta : I64) (len : Usize) : Prop where
  length : 1 ≤ len.val ∧ len.val ≤ 5
  f_value : active62Value f len.val = (inversionTrace (signed62Value params.helpers.modulus) x batches).f
  g_value : active62Value g len.val = (inversionTrace (signed62Value params.helpers.modulus) x batches).g
  eta_value : eta.val = -(inversionTrace (signed62Value params.helpers.modulus) x batches).delta
  f_normalized : active62Normalized f len.val
  g_normalized : active62Normalized g len.val
  f_digits : ∀ k : Fin 5, |f[k.val]!.val| ≤ signedRadix
  g_digits : ∀ k : Fin 5, |g[k.val]!.val| ≤ signedRadix
  f_capacity : |active62Value f len.val| ≤ signedRadix ^ len.val
  g_capacity : |active62Value g len.val| ≤ signedRadix ^ len.val
  d_normalized : signed62Normalized d
  e_normalized : signed62Normalized e
  d_range : -2 * signed62Value params.helpers.modulus < signed62Value d ∧
    signed62Value d < signed62Value params.helpers.modulus
  e_range : -2 * signed62Value params.helpers.modulus < signed62Value e ∧
    signed62Value e < signed62Value params.helpers.modulus
  d_bezout : Int.ModEq (signed62Value params.helpers.modulus) (x * signed62Value d)
    (signed62Value params.r2 * active62Value f len.val)
  e_bezout : Int.ModEq (signed62Value params.helpers.modulus) (x * signed62Value e)
    (signed62Value params.r2 * active62Value g len.val)

theorem inversion_trace_next (modulus x : Int) (batches : Nat) :
    inversionTrace modulus x (batches + 1) = iterate 62 (inversionTrace modulus x batches) := by
  unfold inversionTrace
  rw [Nat.mul_add, Nat.mul_one, iterate_add]

theorem inversion_trace_eta_bound (modulus x : Int) (batches : Nat) (hb : batches ≤ 11) :
    |(inversionTrace modulus x batches).delta| ≤ 683 := by
  have h := iterate_delta_bound (62 * batches) ⟨1, modulus, x⟩
  simp only [show |(1 : Int)| = 1 from by decide, Nat.cast_mul, Nat.cast_ofNat] at h
  unfold inversionTrace
  omega

#print axioms inversion_trace_next
#print axioms inversion_trace_eta_bound
end UdonVerify.CommonSigned62
