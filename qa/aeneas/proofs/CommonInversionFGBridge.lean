import CommonInversion.Funs
import CommonFG62FirstUpdate
import CommonSigned62Roundtrip

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] CommonInversion.field.pasta.safegcd.MASK62
  CommonFG62.field.pasta.safegcd.MASK62 CommonFG62First.field.pasta.safegcd.MASK62
  Signed62Native.field.pasta.safegcd.MASK62

def inversionFGMatrix (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonFG62.field.pasta.safegcd.Trans2x2 := ⟨t.u, t.v, t.q, t.r⟩

def inversionFirstMatrix (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonFG62First.field.pasta.safegcd.Trans2x2 := ⟨t.u, t.v, t.q, t.r⟩

def inversionFirstDict {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P) :
    CommonFG62First.field.pasta.safegcd.InvParams P := ⟨inst.MODULUS_62, inst.MU, inst.R2_62⟩

theorem inversion_fg_update_bridge (len : Usize) (f g : Signed62)
    (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonInversion.field.pasta.safegcd.update_fg_62_var len f g t =
      CommonFG62.field.pasta.safegcd.update_fg_62_var len f g (inversionFGMatrix t) := by rfl

theorem inversion_fg_first_bridge {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P)
    (f g : Signed62) (t : CommonInversion.field.pasta.safegcd.Trans2x2) :
    CommonInversion.field.pasta.safegcd.update_fg_62_first inst f g t =
      CommonFG62First.field.pasta.safegcd.update_fg_62_first (inversionFirstDict inst) f g (inversionFirstMatrix t) := by rfl

theorem inversion_pack_bridge (x : A4) :
    CommonInversion.field.pasta.safegcd.pack62 x = Signed62Native.field.pasta.safegcd.pack62 x := by rfl

theorem inversion_unpack_bridge (x : Signed62) :
    CommonInversion.field.pasta.safegcd.unpack62 x = Signed62Native.field.pasta.safegcd.unpack62 x := by rfl

#print axioms inversion_fg_update_bridge
#print axioms inversion_fg_first_bridge
#print axioms inversion_pack_bridge
#print axioms inversion_unpack_bridge
end UdonVerify.CommonSigned62
