import CommonPublicInversionDictionaries
import CommonSigned62Packing
import CommonFG62Arrays

open Aeneas Std Result UdonVerify.CommonSigned62
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post CommonPublicInversion.field.pasta.safegcd.MASK62
  Signed62Native.field.pasta.safegcd.MASK62

theorem public_signed62_bridge (x : A4) :
    CommonPublicInversion.field.pasta.safegcd.to_signed62 x =
      Signed62Native.field.pasta.safegcd.to_signed62 x := by rfl

theorem signed62_eq_of_digits (lhs rhs : Signed62)
    (hdigits : ∀ k : Fin 5, lhs[k.val]!.val = rhs[k.val]!.val) : lhs = rhs := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp only [lhs.property, rhs.property]
  · intro k hk hk'
    have hbound : k < 5 := by simpa [lhs.property] using hk
    have h := IScalar.eq_of_val_eq (hdigits ⟨k, hbound⟩)
    simpa only [Array.getElem!_Nat_eq, getElem!_pos lhs.val k hk,
      getElem!_pos rhs.val k hk'] using h

theorem public_r2_eq {M : Type} (inst : Modulus M) (limbs : A4) (out : Signed62)
    (hr2 : inst.sealedParametersInst.R2 = ok limbs)
    (hdigits : ∀ k : Fin 5, (packed62Digit limbs k.val : Int) = out[k.val]!.val) :
    CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket.R2_62 inst = ok out := by
  unfold CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket.R2_62
  rw [hr2]
  simp only [bind_ok]
  rw [public_signed62_bridge]
  apply fg_result_eq
  apply WP.spec_mono (to_signed62_digits limbs)
  intro result hresult
  apply signed62_eq_of_digits
  intro k
  exact (hresult k).trans (hdigits k)

theorem public_mu_eq {M : Type} (inst : Modulus M) (inverse : U64)
    (hinverse : inst.sealedParametersInst.MONTGOMERY_INV = ok inverse) :
    CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket.MU inst =
      ok (U64.wrapping_sub 0#u64 inverse &&& 4611686018427387903#u64) := by
  unfold CommonPublicInversion.field.pasta.safegcd.InvParams.Blanket.MU
  rw [hinverse]
  simp only [bind_ok, CommonPublicInversion.core.num.U64.wrapping_neg, NativeField.core.num.U64.wrapping_neg]
  have hmask : CommonPublicInversion.field.pasta.safegcd.MASK62 =
      Signed62Native.field.pasta.safegcd.MASK62 := by rfl
  rw [hmask, mask62_eq]
  simp only [bind_ok]

#print axioms public_signed62_bridge
#print axioms signed62_eq_of_digits
#print axioms public_r2_eq
#print axioms public_mu_eq
end UdonVerify.PublicInversion
