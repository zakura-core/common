import CommonInvParameters
import CommonSigned62Signs
import CommonCoeffWords

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

def coeffRowStart (u v : I64) (d e : Signed62) (mu : U64) : Result (I64 × I128) := do
  let sign ← coeffSignStart u v d[4]! e[4]!
  let row ← fgRowTerm u v d[0]! e[0]!
  ok (coeffCorrectWord mu row sign, row)

@[step]
theorem coeff_row_start_spec (u v : I64) (d e : Signed62) (mu : U64)
    (hrow : |u.val| + |v.val| ≤ signedRadix)
    (hd : signed62Normalized d) (he : signed62Normalized e)
    (hd0 : |d[0]!.val| ≤ signedRadix) (he0 : |e[0]!.val| ≤ signedRadix) :
    coeffRowStart u v d e mu ⦃ out =>
      out.1.val = coeffCorrection u.val v.val (signed62Value d) (signed62Value e)
        (u.val * d[0]!.val + v.val * e[0]!.val) mu.val ∧
      -2 * signedRadix < out.1.val ∧ out.1.val ≤ signedRadix ∧
      out.2.val = u.val * d[0]!.val + v.val * e[0]!.val ∧ |out.2.val| ≤ signedRadix ^ 2 ⦄ := by
  unfold coeffRowStart
  step -grind with (coeff_sign_start_spec u v d[4]! e[4]! hrow) as ⟨sign, hsign, hbound⟩
  step -grind with (fg_row_term_spec u v d[0]! e[0]! hrow hd0 he0) as ⟨row, hvalue, hrowBound⟩
  try simp only [WP.spec_ok]
  obtain ⟨hcorrect, hcorrectLo, hcorrectHi⟩ := coeff_correct_word_value mu row sign hbound
  have hsignFull : sign.val = (if signed62Value d < 0 then u.val else 0) +
      (if signed62Value e < 0 then v.val else 0) := by
    simpa only [← signed62_sign_iff d hd, ← signed62_sign_iff e he] using hsign
  refine ⟨?_, hcorrectLo, hcorrectHi, hvalue, hrowBound⟩
  rw [hcorrect, hsignFull, hvalue]
  rfl

theorem coeff_correction_abs (correction : I64)
    (h : -2 * signedRadix < correction.val ∧ correction.val ≤ signedRadix) :
    |correction.val| ≤ 2 * signedRadix := by
  rw [abs_le]
  have hb : 0 < signedRadix := by norm_num [signedRadix]
  constructor <;> omega

#print axioms coeff_row_start_spec
#print axioms coeff_correction_abs
end UdonVerify.CommonSigned62
