import CommonInvParameters

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

theorem signed62_low_congruence (a : Signed62) :
    Int.ModEq signedRadix (signed62Value a) a[0]!.val := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-(a[1]!.val + signedRadix * a[2]!.val + signedRadix ^ 2 * a[3]!.val +
    signedRadix ^ 3 * a[4]!.val), ?_⟩
  unfold signed62Value
  ring

theorem inversion_radix_has_inverse {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) :
    ∃ inverse : Int, Int.ModEq (signed62Value params.modulus) (inverse * signedRadix) 1 := by
  have hmod := ((signed62_low_congruence params.modulus).mul_right (params.mu.val : Int)).trans params.inverse
  obtain ⟨k, hk⟩ := hmod.dvd
  refine ⟨k, Int.modEq_iff_dvd.mpr ?_⟩
  refine ⟨(params.mu.val : Int), ?_⟩
  nlinarith only [hk]

theorem inversion_cancel_radix {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (left right : Int)
    (h : Int.ModEq (signed62Value params.modulus) (signedRadix * left) (signedRadix * right)) :
    Int.ModEq (signed62Value params.modulus) left right := by
  obtain ⟨inverse, hi⟩ := inversion_radix_has_inverse params
  have hl : Int.ModEq (signed62Value params.modulus) ((inverse * signedRadix) * left) left := by
    simpa only [one_mul] using hi.mul_right left
  have hr : Int.ModEq (signed62Value params.modulus) ((inverse * signedRadix) * right) right := by
    simpa only [one_mul] using hi.mul_right right
  apply hl.symm.trans
  apply Int.ModEq.trans _ hr
  simpa only [mul_assoc] using h.mul_left inverse

theorem coefficient_row_bezout {P : Type} {inst : CommonInvHelpers.field.pasta.safegcd.InvParams P}
    (params : InvHelperParameters inst) (x scale f g d e fNew dNew u v : Int)
    (hd : Int.ModEq (signed62Value params.modulus) (x * d) (scale * f))
    (he : Int.ModEq (signed62Value params.modulus) (x * e) (scale * g))
    (hrow : signedRadix * fNew = u * f + v * g)
    (hcoeff : Int.ModEq (signed62Value params.modulus) (signedRadix * dNew) (u * d + v * e)) :
    Int.ModEq (signed62Value params.modulus) (x * dNew) (scale * fNew) := by
  apply inversion_cancel_radix params
  have hlinear := (hd.mul_left u).add (he.mul_left v)
  have hscaled := hcoeff.mul_left x
  have hmiddle : Int.ModEq (signed62Value params.modulus) (x * (u * d + v * e))
      (scale * (u * f + v * g)) := by
    convert hlinear using 1 <;> ring
  have hcombined := hscaled.trans hmiddle
  rw [← hrow] at hcombined
  convert hcombined using 1 <;> ring

#print axioms signed62_low_congruence
#print axioms inversion_radix_has_inverse
#print axioms inversion_cancel_radix
#print axioms coefficient_row_bezout
end UdonVerify.CommonSigned62
