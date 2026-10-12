import CommonInversion.Funs
import CommonDivstepFull

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def inversionNativeMatrix (t : CommonDivsteps.field.pasta.safegcd.Trans2x2) :
    CommonInversion.field.pasta.safegcd.Trans2x2 := ⟨t.u, t.v, t.q, t.r⟩

def inversionDivstepMatrix (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonDivsteps.field.pasta.safegcd.Trans2x2 := ⟨t.u, t.v, t.q, t.r⟩

theorem inversion_divsteps_loop_bridge (eta : I64) (f0 g0 u v q r f g : U64) (remaining : U32) :
    CommonInversion.field.pasta.safegcd.divsteps_62_var_loop eta f0 g0 u v q r f g remaining =
      CommonDivsteps.field.pasta.safegcd.divsteps_62_var_loop eta f0 g0 u v q r f g remaining := by rfl

theorem inversion_divsteps_bridge (eta : I64) (f0 g0 : U64) :
    CommonInversion.field.pasta.safegcd.divsteps_62_var eta f0 g0 =
      (do let out ← CommonDivsteps.field.pasta.safegcd.divsteps_62_var eta f0 g0
          ok (inversionNativeMatrix out.1, out.2)) := by
  unfold CommonInversion.field.pasta.safegcd.divsteps_62_var CommonDivsteps.field.pasta.safegcd.divsteps_62_var
  rw [inversion_divsteps_loop_bridge]
  simp only [Std.bind_assoc, Bind.bind, lift, bind_ok, Std.uncurry_apply_pair]
  congr 1
  funext values
  rcases values with ⟨eta1, u, v, q, r⟩
  simp only [Std.bind_assoc, Bind.bind, bind_ok, Std.uncurry_apply_pair, inversionNativeMatrix]
  rfl

@[step]
theorem inversion_divsteps_full_spec (eta : I64) (f0 g0 : U64) (f g : Int)
    (he : |eta.val| ≤ 683) (hf : f % 2 = 1)
    (hflow : Int.ModEq signedRadix (f0.val : Int) f)
    (hglow : Int.ModEq signedRadix (g0.val : Int) g) :
    CommonInversion.field.pasta.safegcd.divsteps_62_var eta f0 g0 ⦃ out =>
      NativeBatchResult ⟨-eta.val, f, g⟩ (inversionDivstepMatrix out.1, out.2) ⦄ := by
  rw [inversion_divsteps_bridge]
  apply WP.spec_bind (native_divsteps_full_spec eta f0 g0 f g he hf hflow hglow)
  intro out hout
  simpa only [WP.spec_ok, inversionNativeMatrix, inversionDivstepMatrix] using hout

#print axioms inversion_divsteps_loop_bridge
#print axioms inversion_divsteps_bridge
#print axioms inversion_divsteps_full_spec
end UdonVerify.CommonSigned62
