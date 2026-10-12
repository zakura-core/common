import CommonPublicInversionCore
import CommonInversionEntry

open Aeneas Std Result UdonVerify.CommonSigned62
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def CoreInversionResult {P : Type} {inst : CommonPublicInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters (coreDict inst)) (x : A4) (out : Option A4) : Prop :=
  match out with
  | none => val4 x = 0
  | some limbs => val4 x ≠ 0 ∧ InversionResult params (val4 x : Int) limbs

@[step]
theorem public_core_invert_conditional_spec {P : Type}
    (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (params : InversionParameters (coreDict inst)) (x : A4)
    (hx : (val4 x : Int) < signed62Value params.helpers.modulus)
    (hunit : val4 x ≠ 0 → Int.gcd (signed62Value params.helpers.modulus) (val4 x : Int) = 1)
    (hconverges : (inversionTrace (signed62Value params.helpers.modulus) (val4 x : Int) 12).g = 0) :
    CommonPublicInversion.field.pasta.safegcd.invert inst x ⦃ out => CoreInversionResult params x out ⦄ := by
  unfold CommonPublicInversion.field.pasta.safegcd.invert
  rw [public_counted_bridge]
  apply WP.spec_bind (invert_counted_conditional_spec params x hx hunit hconverges)
  intro counted hcounted
  cases counted with
  | none =>
    simpa only [CommonPublicInversion.core.option.Option.map, WP.spec_ok, CoreInversionResult,
      CountedInversionResult] using hcounted
  | some result =>
    rcases result with ⟨limbs, count⟩
    simp only [CommonPublicInversion.core.option.Option.map,
      CommonPublicInversion.field.pasta.safegcd.invert.closure.Insts.CoreOpsFunctionFnOnceTuplePairArrayU644U32ArrayU644.call_once,
      Std.uncurry_apply_pair, bind_ok, WP.spec_ok, CoreInversionResult]
    exact ⟨hcounted.1, hcounted.2.1⟩

#print axioms public_core_invert_conditional_spec
end UdonVerify.PublicInversion
