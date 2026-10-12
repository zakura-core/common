import CommonInversion.Funs
import CommonCoeffFirstUpdate
import CommonCoeffTerminalUpdate
import CommonNormalize
import CommonShrink
import CommonFGRange

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] CommonInversion.field.pasta.safegcd.MASK62 CommonInvHelpers.field.pasta.safegcd.MASK62

def inversionHelperDict {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P) :
    CommonInvHelpers.field.pasta.safegcd.InvParams P := ⟨inst.MODULUS_62, inst.MU, inst.R2_62⟩

def inversionHelperMatrix (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonInvHelpers.field.pasta.safegcd.Trans2x2 := ⟨t.u, t.v, t.q, t.r⟩

theorem inversion_compare_bridge (a b : Signed62) (len : Usize) (factor : I64) :
    CommonInversion.field.pasta.safegcd.checks.mul_cmp_62 a len b factor =
      CommonInvHelpers.field.pasta.safegcd.checks.mul_cmp_62 a len b factor := by rfl

theorem inversion_fg_range_bridge {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (f g : Signed62) (len : Usize) :
    CommonInversion.field.pasta.safegcd.checks.assert_fg_range inst f g len =
      CommonInvHelpers.field.pasta.safegcd.checks.assert_fg_range (inversionHelperDict inst) f g len := by rfl

theorem inversion_coeff_update_bridge {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (d e : Signed62) (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonInversion.field.pasta.safegcd.update_de_62 inst d e t =
      CommonInvHelpers.field.pasta.safegcd.update_de_62 (inversionHelperDict inst) d e (inversionHelperMatrix t) := by rfl

theorem inversion_coeff_first_bridge {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (e : Signed62) (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonInversion.field.pasta.safegcd.update_de_62_first inst e t =
      CommonInvHelpers.field.pasta.safegcd.update_de_62_first (inversionHelperDict inst) e (inversionHelperMatrix t) := by rfl

theorem inversion_coeff_terminal_bridge {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (d e : Signed62) (u v : I64) :
    CommonInversion.field.pasta.safegcd.update_d_only_62 inst d e u v =
      CommonInvHelpers.field.pasta.safegcd.update_d_only_62 (inversionHelperDict inst) d e u v := by rfl

theorem inversion_normalize_bridge {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (r : Signed62) (sign : I64) :
    CommonInversion.field.pasta.safegcd.normalize_62 inst r sign =
      CommonInvHelpers.field.pasta.safegcd.normalize_62 (inversionHelperDict inst) r sign := by rfl

theorem inversion_zero_bridge (g : Signed62) (len : Usize) :
    CommonInversion.field.pasta.safegcd.is_zero g len = CommonInvHelpers.field.pasta.safegcd.is_zero g len := by rfl

theorem inversion_shrink_bridge (f g : Signed62) (len : Usize) :
    CommonInversion.field.pasta.safegcd.shrink_len f g len =
      CommonInvHelpers.field.pasta.safegcd.shrink_len f g len := by rfl

#print axioms inversion_compare_bridge
#print axioms inversion_fg_range_bridge
#print axioms inversion_coeff_update_bridge
#print axioms inversion_coeff_first_bridge
#print axioms inversion_coeff_terminal_bridge
#print axioms inversion_normalize_bridge
#print axioms inversion_zero_bridge
#print axioms inversion_shrink_bridge
end UdonVerify.CommonSigned62
