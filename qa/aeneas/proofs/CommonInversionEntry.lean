import CommonInversionEntryBridge
import CommonInversionLoop

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def CountedInversionResult {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : A4) (out : Option (A4 × U32)) : Prop :=
  match out with
  | none => val4 x = 0
  | some result => val4 x ≠ 0 ∧ BoundedInversionResult params (val4 x : Int) result

@[step]
theorem invert_counted_conditional_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : A4)
    (hx : (val4 x : Int) < signed62Value params.helpers.modulus)
    (hunit : val4 x ≠ 0 → Int.gcd (signed62Value params.helpers.modulus) (val4 x : Int) = 1)
    (hconverges : (inversionTrace (signed62Value params.helpers.modulus) (val4 x : Int) 12).g = 0) :
    CommonInversion.field.pasta.safegcd.invert_counted inst x ⦃ out => CountedInversionResult params x out ⦄ := by
  rw [inversion_entry_bridge]
  unfold nativeInversionEntry
  apply WP.spec_bind (inversion_zero_array_spec x)
  intro zero hzero
  cases zero with
  | true =>
    simpa only [ite_true, WP.spec_ok, CountedInversionResult] using hzero.mp rfl
  | false =>
    have hnz : val4 x ≠ 0 := fun h => Bool.false_ne_true (hzero.mpr h)
    have hbound : val4 x < 2 ^ 255 := by
      have hm := params.helpers.bound
      omega
    simp only [Bool.false_eq_true, ite_false]
    have hmodulus : inst.MODULUS_62 = ok params.helpers.modulus := params.helpers.modulus_eq
    rw [hmodulus]
    simp only [bind_ok]
    rw [inversion_pack_bridge]
    apply WP.spec_bind (pack62_spec x hbound)
    intro g hg
    rw [params.r2_eq]
    simp only [bind_ok]
    apply WP.spec_bind (native_first_spec params (val4 x : Int) g hg.1 hg.2.1 ⟨by omega, hx⟩ (hunit hnz))
    intro first hfirst
    simp only [core.ops.range.RangeInclusive.new, bind_ok]
    apply WP.spec_bind (inversion_loop_spec params (val4 x : Int) 1 2#u32
      first.f first.g first.d first.e first.eta first.len (by decide) (by decide) hfirst
      ⟨by omega, hx⟩ (hunit hnz) hconverges)
    intro out hout
    simp [WP.spec_ok, CountedInversionResult, hnz, hout]

#print axioms invert_counted_conditional_spec
end UdonVerify.CommonSigned62
