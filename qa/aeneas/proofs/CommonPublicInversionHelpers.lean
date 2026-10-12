import CommonPublicInversion.Funs
import CommonInversionInvBridge
import CommonInversionDivstepBridge

open Aeneas Std Result UdonVerify.CommonSigned62
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option allowUnsafeReducibility true
attribute [local reducible] CommonPublicInversion.field.pasta.safegcd.MASK62
  CommonInversion.field.pasta.safegcd.MASK62

def coreDict {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P) :
    CommonInversion.field.pasta.safegcd.InvParams P := ⟨inst.MODULUS_62, inst.MU, inst.R2_62⟩

def toCoreMatrix (t : CommonPublicInversion.field.pasta.safegcd.Trans2x2) :
    CommonInversion.field.pasta.safegcd.Trans2x2 := ⟨t.u, t.v, t.q, t.r⟩

def fromCoreMatrix (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonPublicInversion.field.pasta.safegcd.Trans2x2 := ⟨t.u, t.v, t.q, t.r⟩

theorem public_fg_update_bridge (len : Usize) (f g : Signed62)
    (t : CommonPublicInversion.field.pasta.safegcd.Trans2x2) :
    CommonPublicInversion.field.pasta.safegcd.update_fg_62_var len f g t =
      CommonInversion.field.pasta.safegcd.update_fg_62_var len f g (toCoreMatrix t) := by rfl

theorem public_fg_first_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (f g : Signed62) (t : CommonPublicInversion.field.pasta.safegcd.Trans2x2) :
    CommonPublicInversion.field.pasta.safegcd.update_fg_62_first inst f g t =
      CommonInversion.field.pasta.safegcd.update_fg_62_first (coreDict inst) f g (toCoreMatrix t) := by rfl

theorem public_coefficient_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (d e : Signed62) (t : CommonPublicInversion.field.pasta.safegcd.Trans2x2) :
    CommonPublicInversion.field.pasta.safegcd.update_de_62 inst d e t =
      CommonInversion.field.pasta.safegcd.update_de_62 (coreDict inst) d e (toCoreMatrix t) := by rfl

theorem public_coefficient_first_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (e : Signed62) (t : CommonPublicInversion.field.pasta.safegcd.Trans2x2) :
    CommonPublicInversion.field.pasta.safegcd.update_de_62_first inst e t =
      CommonInversion.field.pasta.safegcd.update_de_62_first (coreDict inst) e (toCoreMatrix t) := by rfl

theorem public_coefficient_terminal_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (d e : Signed62) (u v : I64) :
    CommonPublicInversion.field.pasta.safegcd.update_d_only_62 inst d e u v =
      CommonInversion.field.pasta.safegcd.update_d_only_62 (coreDict inst) d e u v := by rfl

theorem public_range_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (f g : Signed62) (len : Usize) :
    CommonPublicInversion.field.pasta.safegcd.checks.assert_fg_range inst f g len =
      CommonInversion.field.pasta.safegcd.checks.assert_fg_range (coreDict inst) f g len := by rfl

theorem public_compare_bridge (a b : Signed62) (len : Usize) (factor : I64) :
    CommonPublicInversion.field.pasta.safegcd.checks.mul_cmp_62 a len b factor =
      CommonInversion.field.pasta.safegcd.checks.mul_cmp_62 a len b factor := by rfl

theorem public_zero_bridge (a : Signed62) (len : Usize) :
    CommonPublicInversion.field.pasta.safegcd.is_zero a len =
      CommonInversion.field.pasta.safegcd.is_zero a len := by rfl

theorem public_shrink_bridge (f g : Signed62) (len : Usize) :
    CommonPublicInversion.field.pasta.safegcd.shrink_len f g len =
      CommonInversion.field.pasta.safegcd.shrink_len f g len := by rfl

theorem public_normalize_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (a : Signed62) (sign : I64) :
    CommonPublicInversion.field.pasta.safegcd.normalize_62 inst a sign =
      CommonInversion.field.pasta.safegcd.normalize_62 (coreDict inst) a sign := by rfl

theorem public_pack_bridge (x : A4) :
    CommonPublicInversion.field.pasta.safegcd.pack62 x =
      CommonInversion.field.pasta.safegcd.pack62 x := by rfl

theorem public_unpack_bridge (a : Signed62) :
    CommonPublicInversion.field.pasta.safegcd.unpack62 a =
      CommonInversion.field.pasta.safegcd.unpack62 a := by rfl

theorem public_divsteps_loop_bridge (eta : I64) (f0 g0 u v q r f g : U64) (remaining : U32) :
    CommonPublicInversion.field.pasta.safegcd.divsteps_62_var_loop eta f0 g0 u v q r f g remaining =
      CommonInversion.field.pasta.safegcd.divsteps_62_var_loop eta f0 g0 u v q r f g remaining := by rfl

theorem public_divsteps_bridge (eta : I64) (f0 g0 : U64) :
    CommonPublicInversion.field.pasta.safegcd.divsteps_62_var eta f0 g0 =
      (do let out ← CommonInversion.field.pasta.safegcd.divsteps_62_var eta f0 g0
          ok (fromCoreMatrix out.1, out.2)) := by
  unfold CommonPublicInversion.field.pasta.safegcd.divsteps_62_var
    CommonInversion.field.pasta.safegcd.divsteps_62_var
  rw [public_divsteps_loop_bridge]
  simp only [Bind.bind, lift, bind_ok, Std.bind_assoc, Std.uncurry_apply_pair]
  congr 1
  funext values
  rcases values with ⟨eta1, u, v, q, r⟩
  simp only [Bind.bind, bind_ok, Std.bind_assoc, Std.uncurry_apply_pair, fromCoreMatrix]
  rfl

#print axioms public_fg_update_bridge
#print axioms public_fg_first_bridge
#print axioms public_coefficient_bridge
#print axioms public_coefficient_first_bridge
#print axioms public_coefficient_terminal_bridge
#print axioms public_range_bridge
#print axioms public_compare_bridge
#print axioms public_zero_bridge
#print axioms public_shrink_bridge
#print axioms public_normalize_bridge
#print axioms public_pack_bridge
#print axioms public_unpack_bridge
#print axioms public_divsteps_loop_bridge
#print axioms public_divsteps_bridge
end UdonVerify.PublicInversion
