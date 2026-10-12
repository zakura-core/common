import CommonCoeffSpecialMath

open Aeneas Std Result
namespace UdonVerify.CommonSigned62
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024
set_option allowUnsafeReducibility true
attribute [local reducible] WP.Post

/-- Duplicate the live row only to reuse the two-row mathematical specification. -/
def duplicateCoeffRow (u v : I64) : CommonInvHelpers.field.pasta.safegcd.Trans2x2 := ⟨u, v, u, v⟩

def terminalCoeffPrefix {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (d e : Signed62) (u v : I64) : Result CoeffPrefix := do
  let md ← coeffSignStart u v d[4]! e[4]!
  let cd ← fgRowTerm u v d[0]! e[0]!
  let mu ← inst.MU
  let md1 := coeffCorrectWord mu cd md
  let modulus ← inst.MODULUS_62
  let modD0 ← coeffModTerm modulus[0]! md1
  let cd0 ← cd + modD0
  massert (IScalar.hcast .U64 cd0 &&& 4611686018427387903#u64 = 0#u64)
  let cdCarry0 ← cd0 >>> 62#i32
  ok ⟨md1, md1, cdCarry0, cdCarry0⟩

@[step]
theorem terminal_coeff_prefix_spec {P : Type} (inst : CommonInvHelpers.field.pasta.safegcd.InvParams P)
    (params : InvHelperParameters inst) (d e : Signed62) (u v : I64)
    (hnd : signed62Normalized d) (hne : signed62Normalized e)
    (hrd : -2 * signed62Value params.modulus < signed62Value d ∧ signed62Value d < signed62Value params.modulus)
    (hre : -2 * signed62Value params.modulus < signed62Value e ∧ signed62Value e < signed62Value params.modulus)
    (huv : |u.val| + |v.val| ≤ signedRadix) :
    terminalCoeffPrefix inst d e u v ⦃ out =>
      out.md = out.me ∧ out.cd = out.ce ∧ CoeffPrefixPost params d e (duplicateCoeffRow u v) out ⦄ := by
  obtain ⟨hd, _⟩ := inv_coefficient_digit_bounds inst params d hnd hrd
  obtain ⟨he, _⟩ := inv_coefficient_digit_bounds inst params e hne hre
  obtain ⟨hm, _⟩ := inv_modulus_digit_bounds inst params
  have hb : (256 : Int) ≤ signedRadix := by norm_num [signedRadix]
  unfold terminalCoeffPrefix
  step -grind with (coeff_sign_start_spec u v d[4]! e[4]! huv) as ⟨md, hmd, hmdBound⟩
  step -grind with (fg_row_term_spec u v d[0]! e[0]! huv (hd ⟨0, by decide⟩) (he ⟨0, by decide⟩))
    as ⟨cd, hcd, hcdBound⟩
  rw [params.mu_eq]
  simp only [bind_ok]
  generalize hmdDef : coeffCorrectWord params.mu cd md = md1
  obtain ⟨hmd1, hmdLo, hmdHi⟩ := coeff_correct_word_value params.mu cd md hmdBound
  rw [hmdDef] at hmd1 hmdLo hmdHi
  have hmdFull : md.val = (if signed62Value d < 0 then u.val else 0) +
      (if signed62Value e < 0 then v.val else 0) := by
    simpa only [← signed62_sign_iff d hnd, ← signed62_sign_iff e hne] using hmd
  have hmdExact : md1.val = coeffCorrection u.val v.val (signed62Value d) (signed62Value e)
      (u.val * d[0]!.val + v.val * e[0]!.val) params.mu.val := by
    rw [hmd1, hmdFull, hcd]
    rfl
  have hmdAbs := coeff_correction_abs md1 ⟨hmdLo, hmdHi⟩
  rw [params.modulus_eq]
  simp only [bind_ok]
  step -grind with (coeff_mod_term_spec params.modulus[0]! md1 (hm ⟨0, by decide⟩) hmdAbs)
    as ⟨modD0, hmodD0, hmodD0Bound⟩
  step -grind with (coeff_add_mod_spec cd modD0 (by nlinarith only [hcdBound, hb]) hmodD0Bound)
    as ⟨cd0, hcd0, hcd0Bound⟩
  let termD := coeffTerm u.val v.val md1.val d e params.modulus
  have haccD0 : cd0.val = termD 0 := by rw [hcd0, hmodD0, hcd]; rfl
  have hzeroD : termD 0 % signedRadix = 0 := by
    dsimp only [termD, coeffTerm]
    rw [hmdExact]
    exact coeff_correction_cancels _ _ _ _ _ _ _ params.inverse
  have hbitD := fg_row_low_zero cd0 (by rw [haccD0]; exact hzeroD)
  simp only [hbitD, massert, bind_ok, ite_true]
  step -grind with (coeff_shift_spec cd0 hcd0Bound) as ⟨cdCarry0, hcdCarry0, hcdCarry0Bound⟩
  try simp only [WP.spec_ok]
  have hcarryD0 : cdCarry0.val = fgCarry termD 0 := by rw [hcdCarry0, haccD0]; rfl
  exact ⟨hmdExact, hmdExact, hmdAbs, hmdAbs, hcarryD0, hcarryD0,
    hcdCarry0Bound, hcdCarry0Bound, hzeroD, hzeroD⟩

#print axioms terminal_coeff_prefix_spec
end UdonVerify.CommonSigned62
