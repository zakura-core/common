import CommonPublicInversionHelpers

open Aeneas Std Result UdonVerify.CommonSigned62
namespace UdonVerify.PublicInversion
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option allowUnsafeReducibility true
attribute [local irreducible] Std.bind
  CommonPublicInversion.field.pasta.safegcd.divsteps_62_var
  CommonPublicInversion.field.pasta.safegcd.update_fg_62_var
  CommonPublicInversion.field.pasta.safegcd.update_fg_62_first
  CommonPublicInversion.field.pasta.safegcd.update_de_62
  CommonPublicInversion.field.pasta.safegcd.update_de_62_first
  CommonPublicInversion.field.pasta.safegcd.update_d_only_62
  CommonInversion.field.pasta.safegcd.divsteps_62_var
  CommonInversion.field.pasta.safegcd.update_fg_62_var
  CommonInversion.field.pasta.safegcd.update_fg_62_first
  CommonInversion.field.pasta.safegcd.update_de_62
  CommonInversion.field.pasta.safegcd.update_de_62_first
  CommonInversion.field.pasta.safegcd.update_d_only_62
  CommonInversion.field.pasta.safegcd.checks.mul_cmp_62
  CommonInversion.field.pasta.safegcd.checks.assert_fg_range
  CommonInversion.field.pasta.safegcd.is_zero
  CommonInversion.field.pasta.safegcd.normalize_62
  CommonInversion.field.pasta.safegcd.shrink_len
  CommonInversion.field.pasta.safegcd.unpack62

theorem public_loop_body_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (iter : core.ops.range.RangeInclusive U32) (f g d e : Signed62) (eta : I64) (len : Usize) :
    CommonPublicInversion.field.pasta.safegcd.invert_counted_loop.body inst iter f g d e eta len =
      CommonInversion.field.pasta.safegcd.invert_counted_loop.body (coreDict inst) iter f g d e eta len := by
  unfold CommonPublicInversion.field.pasta.safegcd.invert_counted_loop.body
    CommonInversion.field.pasta.safegcd.invert_counted_loop.body
  simp only [public_divsteps_bridge, Bind.bind, lift, Std.bind_assoc, bind_ok, Std.uncurry,
    public_fg_update_bridge, public_zero_bridge, public_coefficient_terminal_bridge,
    public_coefficient_bridge, public_compare_bridge, public_range_bridge, public_shrink_bridge,
    public_normalize_bridge, public_unpack_bridge, toCoreMatrix, fromCoreMatrix,
    CommonPublicInversion.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq,
    CommonInversion.core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
  congr 1

theorem public_loop_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (iter : core.ops.range.RangeInclusive U32) (f g d e : Signed62) (eta : I64) (len : Usize) :
    CommonPublicInversion.field.pasta.safegcd.invert_counted_loop inst iter f g d e eta len =
      CommonInversion.field.pasta.safegcd.invert_counted_loop (coreDict inst) iter f g d e eta len := by
  unfold CommonPublicInversion.field.pasta.safegcd.invert_counted_loop
    CommonInversion.field.pasta.safegcd.invert_counted_loop
  congr 1
  funext state
  rcases state with ⟨iter1, f1, g1, d1, e1, eta1, len1⟩
  simpa only [Std.uncurry_apply_pair] using public_loop_body_bridge inst iter1 f1 g1 d1 e1 eta1 len1

theorem public_counted_bridge {P : Type} (inst : CommonPublicInversion.field.pasta.safegcd.InvParams P)
    (x : A4) :
    CommonPublicInversion.field.pasta.safegcd.invert_counted inst x =
      CommonInversion.field.pasta.safegcd.invert_counted (coreDict inst) x := by
  unfold CommonPublicInversion.field.pasta.safegcd.invert_counted
    CommonInversion.field.pasta.safegcd.invert_counted
  simp only [public_divsteps_bridge, Bind.bind, lift, Std.bind_assoc, bind_ok, Std.uncurry,
    public_pack_bridge, public_fg_first_bridge, public_zero_bridge, public_coefficient_first_bridge,
    public_range_bridge, public_shrink_bridge, public_loop_bridge, toCoreMatrix, fromCoreMatrix, coreDict]
  congr 1

#print axioms public_loop_body_bridge
#print axioms public_loop_bridge
#print axioms public_counted_bridge
end UdonVerify.PublicInversion
