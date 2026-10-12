import CommonInversionFirstBind
import CommonInversionZero

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post
attribute [local irreducible] Std.bind
attribute [local irreducible] CommonInversion.field.pasta.safegcd.divsteps_62_var
  CommonInversion.field.pasta.safegcd.update_fg_62_first
  CommonInversion.field.pasta.safegcd.is_zero
  CommonInversion.field.pasta.safegcd.update_de_62_first
  CommonInversion.field.pasta.safegcd.checks.assert_fg_range
  CommonInversion.field.pasta.safegcd.shrink_len
  CommonInversion.field.pasta.safegcd.invert_counted_loop

def nativeInversionEntry {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P) (x : A4) :
    Result (Option (A4 × U32)) := do
  let zero ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 x inversionZero
  if zero then ok none else do
    let modulus ← inst.MODULUS_62
    let g ← CommonInversion.field.pasta.safegcd.pack62 x
    let r2 ← inst.R2_62
    let first ← nativeInversionFirst inst modulus g r2
    let iter ← core.ops.range.RangeInclusive.new 2#u32 12#u32
    let out ← CommonInversion.field.pasta.safegcd.invert_counted_loop inst iter
      first.f first.g first.d first.e first.eta first.len
    ok (some out)

theorem inversion_entry_bridge {P : Type} (inst : CommonInversion.field.pasta.safegcd.InvParams P) (x : A4) :
    CommonInversion.field.pasta.safegcd.invert_counted inst x = nativeInversionEntry inst x := by
  unfold CommonInversion.field.pasta.safegcd.invert_counted nativeInversionEntry inversionZero
  simp only [lift, bind_ok]
  apply congrArg (Std.bind (core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 x
    (Array.repeat 4#usize 0#u64)))
  funext zero
  cases zero with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    apply congrArg (Std.bind inst.MODULUS_62)
    funext modulus
    apply congrArg (Std.bind (CommonInversion.field.pasta.safegcd.pack62 x))
    funext g
    apply congrArg (Std.bind inst.R2_62)
    funext r2
    have hfirst := inversion_first_bind_eq inst modulus g r2 (fun first => do
      let iter ← core.ops.range.RangeInclusive.new 2#u32 12#u32
      let out ← CommonInversion.field.pasta.safegcd.invert_counted_loop inst iter
        first.f first.g first.d first.e first.eta first.len
      ok (some out))
    refine Eq.trans ?_ hfirst.symm
    simp only [Bind.bind, lift, bind_ok, Std.bind_assoc, Std.uncurry]
    congr 1

#print axioms inversion_entry_bridge
end UdonVerify.CommonSigned62
