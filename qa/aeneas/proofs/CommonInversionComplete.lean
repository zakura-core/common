import CommonInversionEntry
import Divsteps255Convergence

open Aeneas Std Result UdonVerify.SafeGcd
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 1024

theorem inversion_converges {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int)
    (hx : 0 ≤ x ∧ x < signed62Value params.helpers.modulus) :
    (inversionTrace (signed62Value params.helpers.modulus) x 12).g = 0 := by
  change (iterate 744 ⟨1, signed62Value params.helpers.modulus, x⟩).g = 0
  exact divsteps255_converges_744 _ _ params.helpers.positive
    (_root_.le_of_lt params.helpers.bound) params.odd hx.1 (_root_.le_of_lt hx.2)

@[step]
theorem inversion_loop_complete_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : Int) (batches : Nat) (start : U32)
    (f g d e : Signed62) (eta : I64) (len : Usize)
    (hb : 1 ≤ batches ∧ batches ≤ 11) (hstart : start.val = batches + 1)
    (hinv : InversionInvariant params x batches f g d e eta len)
    (hx : 0 ≤ x ∧ x < signed62Value params.helpers.modulus)
    (hgcd : Int.gcd (signed62Value params.helpers.modulus) x = 1) :
    CommonInversion.field.pasta.safegcd.invert_counted_loop inst (inversionRange start) f g d e eta len ⦃ out =>
      BoundedInversionResult params x out ⦄ := by
  exact inversion_loop_spec params x batches start f g d e eta len hb hstart hinv hx hgcd
    (inversion_converges params x hx)

@[step]
theorem invert_counted_spec {P : Type} {inst : CommonInversion.field.pasta.safegcd.InvParams P}
    (params : InversionParameters inst) (x : A4)
    (hx : (val4 x : Int) < signed62Value params.helpers.modulus)
    (hunit : val4 x ≠ 0 → Int.gcd (signed62Value params.helpers.modulus) (val4 x : Int) = 1) :
    CommonInversion.field.pasta.safegcd.invert_counted inst x ⦃ out => CountedInversionResult params x out ⦄ := by
  exact invert_counted_conditional_spec params x hx hunit (inversion_converges params (val4 x : Int) ⟨by omega, hx⟩)

#print axioms inversion_converges
#print axioms inversion_loop_complete_spec
#print axioms invert_counted_spec
end UdonVerify.CommonSigned62
